use std::alloc::{GlobalAlloc, Layout, System};
use std::env;
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

struct CountingAllocator;

static TRACKING: AtomicBool = AtomicBool::new(false);
static ALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static ALLOC_ZEROED_CALLS: AtomicU64 = AtomicU64::new(0);
static REALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static DEALLOC_CALLS: AtomicU64 = AtomicU64::new(0);
static REQUESTED_BYTES: AtomicU64 = AtomicU64::new(0);
static CURRENT_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);
static PEAK_LIVE_BYTES: AtomicUsize = AtomicUsize::new(0);

fn update_peak(current: usize) {
    let mut peak = PEAK_LIVE_BYTES.load(Ordering::Relaxed);
    while current > peak {
        match PEAK_LIVE_BYTES.compare_exchange_weak(
            peak,
            current,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(observed) => peak = observed,
        }
    }
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let tracking = TRACKING.load(Ordering::Relaxed);
        if tracking {
            ALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            REQUESTED_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        }
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            let current =
                CURRENT_LIVE_BYTES.fetch_add(layout.size(), Ordering::Relaxed) + layout.size();
            if tracking {
                update_peak(current);
            }
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let tracking = TRACKING.load(Ordering::Relaxed);
        if tracking {
            ALLOC_ZEROED_CALLS.fetch_add(1, Ordering::Relaxed);
            REQUESTED_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        }
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            let current =
                CURRENT_LIVE_BYTES.fetch_add(layout.size(), Ordering::Relaxed) + layout.size();
            if tracking {
                update_peak(current);
            }
        }
        ptr
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let tracking = TRACKING.load(Ordering::Relaxed);
        if tracking {
            REALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
            REQUESTED_BYTES.fetch_add(new_size as u64, Ordering::Relaxed);
        }
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            let current = if new_size >= layout.size() {
                CURRENT_LIVE_BYTES.fetch_add(new_size - layout.size(), Ordering::Relaxed) + new_size
                    - layout.size()
            } else {
                CURRENT_LIVE_BYTES.fetch_sub(layout.size() - new_size, Ordering::Relaxed)
                    - (layout.size() - new_size)
            };
            if tracking {
                update_peak(current);
            }
        }
        new_ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if TRACKING.load(Ordering::Relaxed) {
            DEALLOC_CALLS.fetch_add(1, Ordering::Relaxed);
        }
        CURRENT_LIVE_BYTES.fetch_sub(layout.size(), Ordering::Relaxed);
        unsafe { System.dealloc(ptr, layout) };
    }
}

#[global_allocator]
static GLOBAL: CountingAllocator = CountingAllocator;

fn reset_counters() -> usize {
    TRACKING.store(false, Ordering::SeqCst);
    ALLOC_CALLS.store(0, Ordering::Relaxed);
    ALLOC_ZEROED_CALLS.store(0, Ordering::Relaxed);
    REALLOC_CALLS.store(0, Ordering::Relaxed);
    DEALLOC_CALLS.store(0, Ordering::Relaxed);
    REQUESTED_BYTES.store(0, Ordering::Relaxed);
    let baseline = CURRENT_LIVE_BYTES.load(Ordering::Relaxed);
    PEAK_LIVE_BYTES.store(baseline, Ordering::Relaxed);
    TRACKING.store(true, Ordering::SeqCst);
    baseline
}

fn main() {
    let input = env::args().nth(1).expect("missing input file");
    let iterations: usize = env::args()
        .nth(2)
        .unwrap_or_else(|| "20".to_owned())
        .parse()
        .expect("iteration count must be positive");
    let warmups: usize = env::args()
        .nth(3)
        .unwrap_or_else(|| "1".to_owned())
        .parse()
        .expect("warmup count must be non-negative");
    assert!(iterations > 0, "iteration count must be positive");

    for _ in 0..warmups {
        black_box(descend::compile_measured(&input).expect("warmup compilation failed"));
    }

    let baseline_live_bytes = reset_counters();
    let mut arena_allocated_bytes = None;
    let mut cuda_len = 0;

    for _ in 0..iterations {
        let sample =
            descend::compile_measured(black_box(&input)).expect("measured compilation failed");
        arena_allocated_bytes = sample.arena_allocated_bytes;
        cuda_len = sample.cuda.len();
        black_box(sample.cuda);
    }

    TRACKING.store(false, Ordering::SeqCst);
    let current_live_bytes = CURRENT_LIVE_BYTES.load(Ordering::Relaxed);
    let peak_live_bytes = PEAK_LIVE_BYTES.load(Ordering::Relaxed);
    let live_delta_bytes = current_live_bytes as i128 - baseline_live_bytes as i128;
    let arena_bytes = arena_allocated_bytes
        .map(|bytes| bytes.to_string())
        .unwrap_or_else(|| "null".to_owned());

    println!(
        concat!(
            "{{\"iterations\":{},\"warmups\":{},",
            "\"alloc_calls\":{},\"alloc_zeroed_calls\":{},",
            "\"realloc_calls\":{},\"dealloc_calls\":{},",
            "\"requested_bytes\":{},\"baseline_live_bytes\":{},",
            "\"current_live_bytes\":{},\"live_delta_bytes\":{},",
            "\"peak_live_bytes\":{},\"peak_growth_bytes\":{},",
            "\"arena_allocated_bytes\":{},\"cuda_len\":{}}}"
        ),
        iterations,
        warmups,
        ALLOC_CALLS.load(Ordering::Relaxed),
        ALLOC_ZEROED_CALLS.load(Ordering::Relaxed),
        REALLOC_CALLS.load(Ordering::Relaxed),
        DEALLOC_CALLS.load(Ordering::Relaxed),
        REQUESTED_BYTES.load(Ordering::Relaxed),
        baseline_live_bytes,
        current_live_bytes,
        live_delta_bytes,
        peak_live_bytes,
        peak_live_bytes.saturating_sub(baseline_live_bytes),
        arena_bytes,
        cuda_len,
    );
}

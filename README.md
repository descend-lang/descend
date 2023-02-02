# Descend
An attempt at safe imperative GPU programming.

## Example: Scaling a Vector
Descend:
```rust
// let reference: &'a mut i32 -- Rust reference type
// let dref: &r w m d -- Descend reference type
// r = lifetime(r) | ident  -- Lifetimes, then variable ident: prv
// w = uniq | shrd -- Uniqueness
// m = cpu.mem | gpu.global | gpu.local | ident -- Memory, then ident: mem
// d = i32 | f64 | ... | ident -- Data Type, then ident: dty
// exec = cpu.thread | gpu.grid | gpu.block | gpu.thread

fn scale_vec<n: nat>(
    h_vec: &uniq cpu.mem [f64; n]
) -[t: cpu.thread]-> () {
    let mut gpu = gpu_device(0);
    let mut a_array = gpu_alloc_copy(&uniq gpu, &shrd *h_vec);
    exec::<64, 1024>(
        &uniq gpu, // which GPU?
        (&uniq a_array,), // Input data as tuple: (&in1, &in2, ..), special case: (&in1,)
        | vec: (&uniq gpu.global [f64; n]) | -[grid: gpu.grid<X<64>, X<1024>>]-> () {
            // View -- allows shaping an array without memory access
            // can be mutable or constant, i.e., to_view_mut(&uniq ...); to_view(&shrd ...)
            // let view = to_view_mut(vec.0): [[f64; n]]
            // group_mut::<1024>(view): [[ [[f64; 1024]]; n/1024]]
            let groups = group_mut::<1024>(to_view_mut(vec.0));
            // g: &uniq gpu.global [[f64; 1024]]
            sched g in groups to block in grid {
                // v: &uniq gpu.global f64
                sched v in g to _ in block {
                    *v = *v * 3.0
                }
            }
        }
    );
    copy_to_host(&shrd a_array, h_vec)
}
```

Generated CUDA code:
```cpp
#include "descend.cuh"
/*
function declarations
*/
template <std::size_t n> auto scale_vec(descend::f64 *const h_vec) -> void;
/*
function defintions
*/
template <std::size_t n> auto scale_vec(descend::f64 *const h_vec) -> void {
  auto gpu = descend::gpu_device(0);
  auto a_array = descend::gpu_alloc_copy<descend::array<descend::f64, n>>(
      (&gpu), (&(*h_vec)));
  descend::exec<64, 1024>(
      (&gpu),
      [] __device__(descend::f64 *const p0, std::size_t n) -> void {
        {
          {
            p0[((blockIdx.x * 1024) + threadIdx.x)] =
                p0[((blockIdx.x * 1024) + threadIdx.x)] * 3.0;
          }
        }
      },
      (&a_array), n);
  descend::copy_to_host<descend::array<descend::f64, n>>((&a_array), h_vec);
}
```

## Setup
Required:
* `clang-format`: Must be found in the system path.
* `rustc` and `cargo`
* `git`

Clone the repository and compile:
```bash
git clone git@github.com:descend-lang/descend.git
cargo build
cargo test
```

## Modules and Directories
ast
---------------------
* Data types and representation of the Abstract Syntax Tree: expressions and types
* Visitors for convenient tree tarversals
* Span tracks the provenance of source code in the AST

parser
---------------------
* parse a string into AST
* based on Rust PEG

ty_check
---------------------
* typing rules restrict how syntactic constructs can be used
* type inference
* borrow checking and lifetime checking are part of type checking/inference
* defines contexts that are tracked during type checking
* pre-declared function signatures for views and built-in functions, such as `exec`


codegen
---------------------
* data types for CUDA AST
* translates Descend AST to CUDA AST: translation cases and functions for all syntactic constructs in Descend
* printing of the CUDA AST: write the AST into a String

cuda-examples/
---------------------
* Contains handwritte or generated CUDA programs
* Contains `descend.cuh`; the header file which is required in order to compile Descend programs,
  that were translated to CUDA, with `nvcc` (contains for example the implementation of `exec`)

descend-examples/
---------------------
* Example programs written in Descend
* Many programs exist twice, once in `with_tys` and once in `infer/`
* with_tys: programs have fully-annotated types
* infer: types in programs are mainly inferred
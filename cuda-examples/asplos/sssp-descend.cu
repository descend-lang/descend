#define GENERATED
#ifdef GENERATED
// Manual adjustment removed <cuda/atomic>
#include "descend.cuh"
#warning "GENERATED is defined." 
#endif

/*  -*- mode: c++ -*-  */
#include <cuda.h>
#include <inttypes.h>
#include <bitset>
#include <cmath>
#include <cassert>
#include "../cub-1.8.0/cub/cub.cuh"
#include "common.h"
#include "csr_graph.h"
#include "support.h"
#include "wl.h"

#define TB_SIZE 768
int CUDA_DEVICE = 0;
int start_node = 0;
char *INPUT, *OUTPUT;

__global__ void kernel(CSRGraph graph, int src) {
	unsigned tid = thread_id_x() + block_id_x() * block_dim_x();
	unsigned nthreads = block_dim_x() * grid_dim_x();

	index_type node_end;
	node_end = (graph).nnodes;
	for (index_type node = 0 + tid; node < node_end; node += nthreads) {
		graph.node_data[node] = (node == src) ? 0 : INF;
	}
}

#define HOR_EDGE 16

#ifdef GENERATED
// Adjust add __forceinine__ to all helper functions
__device__ __forceinline__ void epilog(worklist *wl, descend::u64 m_assignment, descend::u32 work_size, bool coop) {
  wl->epilog(m_assignment, work_size, coop);
}

// Adjust pointer type of worklist to non-const
__device__ __forceinline__ void init_regular(worklist *const wl) {
  wl->init_regular();
}

// Adjust pointer type of worklist to non-const
__device__ __forceinline__ descend::u32 pop_work(worklist *const wl, descend::u32 idx) {
  return wl->pop_work(idx);
}

// Adjust pointer type of worklist to non-const
__device__ __forceinline__ void push_work(worklist *const wl, descend::u32 bag_id, descend::u32 node) {
  wl->push_work(bag_id, node);
}

// Adjust pointer type of worklist to non-const and m_size to be pointer
__device__ __forceinline__ void tb_coop_assign(worklist *const wl, descend::u32 vertex_id, descend::u32 first_edge, descend::u64 m_assignment, descend::u32 * const m_size, descend::u32 tb_coop_lane) {
  // Adjust: manually cast m_size to be pointer to int
  wl->tb_coop_assign(vertex_id, first_edge, m_assignment, *((int *)m_size), tb_coop_lane); 
}

// Adjust pointer type of worklist and CSRGRaph to non-const and m_assignment to be a pointer
__device__ __forceinline__ descend::u32 get_assignment(worklist *const wl, CSRGraph *const graph, descend::u64 * m_assignment, descend::u32 warp_id, descend::u32 * const work_count, descend::u32 total_work) 
{
  // Adjust: cast m_assignment to (unsigned long long *)
  return wl->get_assignment(*graph, *((unsigned long long *)m_assignment), thread_id_x()/32, work_count, total_work);
}

__device__ __forceinline__ descend::i32 thread_load(descend::i32 * const addr) {
  return cub::ThreadLoad<cub::LOAD_CG>(addr);
}

// Adjust: make warp_offset and warp_total pointers
__device__ __forceinline__ void cub_exclusive_sum(cub::WarpScan<int>::TempStorage * const storage, descend::u32 m_size, descend::u32 * const warp_offset, descend::u32 *const warp_total) {
  // Adjust: cast warp_offset and warp_total
  cub::WarpScan<int>(*storage).ExclusiveSum(m_size, *(int *)warp_offset, *(int *)warp_total);
}

__device__ __forceinline__ descend::u32 dist_to_bag_id_int(worklist * const wl, descend::u32 bag_id, descend::i32 dst_dist) {
    return wl->dist_to_bag_id_int(bag_id, dst_dist);
}

// Adjustment: comment out
//template <std::size_t sm_count>
// Adjustment: make wl, graph and work_count non const
// Adjustment: __forceinline__
__device__ __forceinline__ auto sssp_kernel(CSRGraph *const graph,
                            worklist *const wl,
                            descend::u32 *const work_count,
                            descend::u8 *const leader_lane_tb_storage,
// Adjust: rename TempStorage to cub::WarpScan<int>::TempStorage
                            cub::WarpScan<int>::TempStorage *const temp_storage) -> void {
  {
    init_regular(wl);
    {
      // Adjust: comment out, not required
      //descend::Warp $warp = descend::to_warps();
      descend::u32 total_work;
      { total_work = 0u; }

      const auto tb_coop_threshold =
          max((32u * 4u), (((*graph).nedges / (*graph).nnodes) * 4u));
      while (true) {
        descend::u64 m_assignment;
        { m_assignment = 0ull; }

        const auto num =
            //Adjust take reference of m_assignment because of wrong signature for get_assignment
            get_assignment(wl, graph, &m_assignment, descend::get_warp_id(),
                           work_count, total_work);
        const auto ptr = agm_get_real_ptr(m_assignment);
        const auto src_bag_id = agm_get_bag_id(m_assignment);
        descend::u32 m_first_edge;
        descend::u32 m_size;
        descend::u32 m_vertex;
        {
          m_size = 0u;
          // Adjust: remove namespace descend from get_lane_id
          const auto wl_offset = get_lane_id();
          if ((wl_offset < num)) {
            m_vertex = pop_work(wl, (ptr + wl_offset));
            if ((m_vertex < (*graph).nnodes)) {
              m_first_edge = (*graph).row_start[m_vertex];
              m_size = ((*graph).row_start[(m_vertex + 1)] - m_first_edge);
              total_work = (total_work + 1u);
            }
          }
        }

        auto process_mask = descend::ballot_sync((m_size >= tb_coop_threshold));
        const auto tb_coop_lane = find_ms_bit(process_mask);
        {
          if ((tb_coop_lane != 4294967295u)) {
            //Adjust: take pointer of m_size
            tb_coop_assign(wl, m_vertex, m_first_edge, m_assignment, &m_size,
                           tb_coop_lane);
          }
        }

        process_mask = descend::ballot_sync((m_size >= 16u));
        while ((process_mask != 0u)) {
          const auto leader = find_ms_bit(process_mask);
          const auto leader_first_edge =
              descend::shfl_sync(m_first_edge, leader);
          const auto leader_size = descend::shfl_sync(m_size, leader);
          const auto leader_vertex = descend::shfl_sync(m_vertex, leader);
          {
            {
              // Adjust:: remove namespace descend in front of get_lane_id()
              auto offset = get_lane_id();
              while ((offset < leader_size)) {
                const auto edge = (leader_first_edge + offset);
                const auto dst = (*graph).edge_dst[edge];
                const auto wt = (*graph).edge_data[edge];
                const auto new_dist =
                    (thread_load((&(*graph).node_data[leader_vertex])) + wt);
                const auto dst_dist = thread_load((&(*graph).node_data[dst]));
                if ((dst_dist > new_dist)) {
                  atomicMin((&(*graph).node_data[dst]), new_dist);
                  const auto dst_bag_id =
                      dist_to_bag_id_int(wl, src_bag_id, new_dist);
                  push_work(wl, dst_bag_id, dst);
                }

                offset = (offset + 32u);
              }
            }

            process_mask = set_bits(process_mask, 0u, leader, 1u);
          }
        }

        {
          if ((m_size >= 16u)) {
            m_size = 0u;
          }
        }

        // Adjust: substitute __synchtreads with __syncwarp
        __syncwarp();
        descend::u32 warp_offset;
        descend::u32 warp_total;
        warp_offset = 0u;
        warp_total = 0u;
        // Adjust: subsitute warpIdx with descend::get_warp_id
        cub_exclusive_sum((&temp_storage[(descend::get_warp_id() - 0)]), m_size, &warp_offset,
                          &warp_total);
        {
          auto write_idx = warp_offset;
          const auto write_end = (warp_offset + m_size);
          while ((write_idx < write_end)) {
            // Adjust: swap warpIdx for get_warp_id()
            leader_lane_tb_storage[(((descend::get_warp_id() - 0) * (32 * 32)) + write_idx)] =
                // Adjust: remove namespace in front of get_lane_id
                (descend::u8)(get_lane_id());
            write_idx = (write_idx + 1u);
          }
        }

        // Adjust: substitute __synchtreads with __syncwarp
        __syncwarp();
        {
          auto read_idx_start = 0u;
          while ((read_idx_start < warp_total)) {
            descend::u32 m_read_idx;
            descend::u32 leader;
            {
              //Adjust: remove namespace in front of get_lane_id
              m_read_idx = (read_idx_start + get_lane_id());
              leader = (descend::u32)(leader_lane_tb_storage[(
                  // Adjust: swap warpIdx for get_warp_id()
                  ((descend::get_warp_id() - 0) * (32 * 32)) + m_read_idx)]);
            }

            const auto leader_warp_offset =
                descend::shfl_sync(warp_offset, leader);
            const auto leader_first_edge =
                descend::shfl_sync(m_first_edge, leader);
            const auto leader_vertex = descend::shfl_sync(m_vertex, leader);
            {
              if ((m_read_idx < warp_total)) {
                const auto offset = (m_read_idx - leader_warp_offset);
                const auto edge = (leader_first_edge + offset);
                const auto dst = (*graph).edge_dst[edge];
                const auto wt = (*graph).edge_data[edge];
                const auto new_dist =
                    (thread_load((&(*graph).node_data[leader_vertex])) + wt);
                const auto dst_dist = thread_load((&(*graph).node_data[dst]));
                if ((dst_dist > new_dist)) {
                  atomicMin((&(*graph).node_data[dst]), new_dist);
                  const auto dst_bag_id =
                      dist_to_bag_id_int(wl, src_bag_id, new_dist);
                  push_work(wl, dst_bag_id, dst);
                }
              }
            }

            read_idx_start = (read_idx_start + 32u);
          }
        }

        // Adjust: substitute __synchtreads with __syncwarp
        __syncwarp();
        epilog(wl, m_assignment, num, false);
      }
    }
  }
}

// 3. Manual adjustment: Added wrapper kernel. Completely handwritten.
// Adjust: add launch bounds
__launch_bounds__(896, 1)
__global__ void kernel_wrapper(
                            CSRGraph graph,
                            worklist wl,
                            descend::u32 *const work_count) {
  extern __shared__ descend::byte buffer[];
  cub::WarpScan<int>::TempStorage *const tmp = (cub::WarpScan<int>::TempStorage *)(&buffer[0]);
  descend::u8 *const leader_lane_storage  = (descend::u8 *) &tmp[TB_SIZE/32];

  sssp_kernel(&graph, &wl, work_count, leader_lane_storage, tmp);
}

#else

__launch_bounds__(896, 1)
__global__ void sssp_kernel(CSRGraph graph, worklist wl, unsigned* work_count) {
	wl.init_regular();

	unsigned tid = thread_id_x() + block_id_x() * block_dim_x();
	const int warpid = thread_id_x() / 32;
	unsigned total_work = 0;
	__shared__ unsigned char leader_lane_tb_storage[TB_SIZE * 32];
	unsigned char * leader_lane_storage = &(leader_lane_tb_storage[warpid * 32 * 32]);
	unsigned tb_coop_threshold = max(32 * TB_COOP_MUL, (graph.nedges / graph.nnodes) * TB_COOP_MUL);
	while (1) {
		//get work
		unsigned long long m_assignment;
		unsigned num = wl.get_assignment(graph, m_assignment, warpid, work_count, total_work);
		unsigned ptr = agm_get_real_ptr(m_assignment);
		unsigned src_bag_id = agm_get_bag_id(m_assignment);
		uint wl_offset = get_lane_id();
		int m_first_edge;
		int m_size = 0;
		int m_vertex;
		if (wl_offset < num) {
			m_vertex = wl.pop_work(ptr + wl_offset);
			if (m_vertex < graph.nnodes) {
				m_first_edge = graph.row_start[m_vertex];
				m_size = graph.row_start[m_vertex + 1] - m_first_edge;
				total_work++;
			}
		}


		//do tb coop assign, assign just one if multiple
		unsigned process_mask = __ballot_sync(FULL_MASK, m_size >= tb_coop_threshold);
		unsigned tb_coop_lane = find_ms_bit(process_mask);
		if (tb_coop_lane != NOT_FOUND) {
			wl.tb_coop_assign(m_vertex, m_first_edge, m_assignment, m_size, tb_coop_lane);
		}

		 process_mask = __ballot_sync(FULL_MASK, m_size >= HOR_EDGE);
		while (process_mask != 0) {
			unsigned leader = find_ms_bit(process_mask);
			int leader_first_edge = __shfl_sync(FULL_MASK, m_first_edge, leader);
			int leader_size = __shfl_sync(FULL_MASK, m_size, leader);
			int leader_vertex = __shfl_sync(FULL_MASK, m_vertex, leader);
			for (int offset = get_lane_id(); offset < leader_size; offset += 32) {
				index_type edge = leader_first_edge + offset;
				index_type dst = graph.edge_dst[edge];
				edge_data_type wt = graph.edge_data[edge];
				node_data_type new_dist = cub::ThreadLoad<cub::LOAD_CG>(&(graph.node_data[leader_vertex])) + wt;
				node_data_type dst_dist = cub::ThreadLoad<cub::LOAD_CG>(&(graph.node_data[dst]));
				if (dst_dist > new_dist) {
					atomicMin(&(graph.node_data[dst]), new_dist);
					unsigned dst_bag_id = wl.dist_to_bag_id_int(src_bag_id, new_dist);
					wl.push_work(dst_bag_id, dst);
				}
			}
			process_mask = set_bits(process_mask, 0, leader, 1);
		}
		if (m_size >= HOR_EDGE) {
			m_size = 0;
		}
		__syncwarp();
		int warp_offset;
		int warp_total;
		typedef cub::WarpScan<int> WarpScan;
		__shared__ typename WarpScan::TempStorage temp_storage[TB_SIZE / 32];
		WarpScan(temp_storage[warpid]).ExclusiveSum(m_size, warp_offset, warp_total);

		//write the target lane storage
		int write_idx = warp_offset;
		int write_end = warp_offset + m_size;
		while (write_idx < write_end) {
			leader_lane_storage[write_idx] = (unsigned char) get_lane_id();
			write_idx++;
		}
		__syncwarp();
		for (int read_idx_start = 0; read_idx_start < warp_total; read_idx_start += 32) {
			int m_read_idx = read_idx_start + get_lane_id();
			int leader = (int) leader_lane_storage[m_read_idx];
			int leader_warp_offset = __shfl_sync(FULL_MASK, warp_offset, leader);
			int leader_first_edge = __shfl_sync(FULL_MASK, m_first_edge, leader);
			int leader_vertex = __shfl_sync(FULL_MASK, m_vertex, leader);
			if (m_read_idx < warp_total) {
				int offset = m_read_idx - leader_warp_offset;
				index_type edge = leader_first_edge + offset;
				index_type dst = graph.edge_dst[edge];
				edge_data_type wt = graph.edge_data[edge];
				node_data_type new_dist = cub::ThreadLoad<cub::LOAD_CG>(&(graph.node_data[leader_vertex])) + wt;
				node_data_type dst_dist = cub::ThreadLoad<cub::LOAD_CG>(&(graph.node_data[dst]));
				if (dst_dist > new_dist) {
					atomicMin(&(graph.node_data[dst]), new_dist);
					unsigned dst_bag_id = wl.dist_to_bag_id_int(src_bag_id, new_dist);
					wl.push_work(dst_bag_id, dst);
				}
			}
		}
		__syncwarp();
		//free
		wl.epilog(m_assignment, num, false);
	}
}
#endif

__global__ void driver_kernel(int num_tb, int num_threads, worklist wl, CSRGraph gg, uint start_node, unsigned* work_count) {

	cudaStream_t s1;
	cudaStreamCreateWithFlags(&s1, cudaStreamNonBlocking);
	wl_kernel<<<1, 192, 0, s1>>>(wl, start_node);

	cudaStream_t s2;
	cudaStreamCreateWithFlags(&s2, cudaStreamNonBlocking);

#ifdef GENERATED
  unsigned shared_size = TB_SIZE*32 + sizeof(cub::WarpScan<int>::TempStorage) * (TB_SIZE/32);
  printf("Generated Kernel:\n");
  kernel_wrapper<<<num_tb, num_threads, shared_size, s2>>>(gg, wl, work_count); 
#else
  printf("Original Kernel:\n");
	sssp_kernel<<<num_tb, num_threads, 0, s2>>>(gg, wl, work_count);
#endif
}

void gg_main_pipe_1_wrapper(CSRGraph& hg, CSRGraph& gg, uint start_node, int num_tb, int num_threads, worklist wl, unsigned* work_count) {
	// gg_main_pipe_1_gpu<<<1,1>>>(gg,glevel,curdelta,i,DELTA,remove_dups_barrier,remove_dups_blocks,pipe,blocks,threads,cl_curdelta,cl_i, enable_lb);
	//gg_cg_gb<<<gg_main_pipe_1_gpu_gb_blocks, __tb_gg_main_pipe_1_gpu_gb>>>(
	//		gg, glevel, curdelta, i, DELTA, pipe, cl_curdelta, cl_i, enable_lb);

	driver_kernel<<<1, 1>>>(num_tb, num_threads, wl, gg, start_node, work_count);
	cudaDeviceSynchronize();
}

#define I_TIME 4
#define N_TIME 2
__global__ void profiler_kernel(CSRGraph gg, float* bk_wt, int warp_edge_interval) {
	unsigned tid = thread_id_x() + block_id_x() * block_dim_x();
	int warp_id = tid / 32;
	int num_warp = block_dim_x() * grid_dim_x() / 32;

	typedef cub::BlockReduce<float, 1024> BlockReduce;
	__shared__ typename BlockReduce::TempStorage temp_storage;
	float thread_data[I_TIME];
	float tb_ave = 0;
	//find ave weight
	tb_ave = 0;
	for (int n = 0; n < N_TIME; n++) {
		for (int i = 0; i < I_TIME; i++) {
			unsigned warp_offset = ((n * I_TIME + i) * num_warp + warp_id) * warp_edge_interval;
			unsigned edge_id = warp_offset + cub::LaneId();
			if (edge_id < gg.nedges) {
				thread_data[i] = (float) gg.edge_data[edge_id];
			} else {
				thread_data[i] = 0;
			}
		}
		//do a reduction
		float sum = BlockReduce(temp_storage).Sum(thread_data);
		tb_ave += (sum / 1024 / I_TIME);
	}
	tb_ave = tb_ave / N_TIME;
	//store it back
	if (threadIdx.x == 0) {
		bk_wt[blockIdx.x] = tb_ave;
	}
}

void gg_main(CSRGraph& hg, CSRGraph& gg) {

	struct cudaDeviceProp dev_prop;
	cudaGetDeviceProperties(&dev_prop, CUDA_DEVICE);

	int num_threads = TB_SIZE;
	int num_tb_per_sm;
	int max_num_threads;
	int min_grid_size;
#ifdef GENERATED
  unsigned shared_size = TB_SIZE*32 + sizeof(cub::WarpScan<int>::TempStorage) * (TB_SIZE/32);
	check_cuda(cudaOccupancyMaxPotentialBlockSize(&min_grid_size, &max_num_threads, kernel_wrapper, shared_size));
#else
	check_cuda(cudaOccupancyMaxPotentialBlockSize(&min_grid_size, &max_num_threads, sssp_kernel));
#endif
    printf("min_grid_size is %d\n", min_grid_size);
	if (num_threads > max_num_threads) {
		printf("error max threads is %d, specified is %d\n", max_num_threads, num_threads);
		fflush(0);
		exit(1);
	}
	printf("max_num_threads is %d\n", max_num_threads);
#ifdef GENERATED
	check_cuda(cudaOccupancyMaxActiveBlocksPerMultiprocessor(&num_tb_per_sm, kernel_wrapper, num_threads, 0));
#else
	check_cuda(cudaOccupancyMaxActiveBlocksPerMultiprocessor(&num_tb_per_sm, sssp_kernel, num_threads, 0));
#endif

	int num_sm = dev_prop.multiProcessorCount;
	int num_tb = num_tb_per_sm * (num_sm - 1);
	int num_warps = num_threads / 32;
	printf("sm count %u, tb per sm %u, tb size %u, num warp %u, total tb %u\n", num_sm, num_tb_per_sm, num_threads, num_warps, num_tb);

#define WL_SIZE_MUL 1.5f
	unsigned suggest_size = (unsigned)((float)hg.nedges * WL_SIZE_MUL) + (NUM_BAG * BLOCK_SIZE * 8);
	suggest_size = min(suggest_size, 536870912);
	unsigned* work_count;
	check_cuda(cudaMalloc((void **) &work_count, num_tb * num_threads * sizeof(unsigned)));

#define RUN_LOOP 8

	FILE * d3;
	d3 = fopen("/dev/fd/3", "a");

	worklist wl;
	wl.alloc(num_tb, num_warps, suggest_size, hg.nnodes, hg.nedges);

	unsigned long long agg_total_work = 0;
	float agg_time = 0;
	for (int loop = 0; loop < RUN_LOOP; loop++) {
		int other_num_tb = num_tb_per_sm * num_sm;

		kernel<<<other_num_tb, 1024>>>(gg, start_node);
		check_cuda(cudaMemset(work_count, 0, num_tb * num_threads * sizeof(unsigned)));
		wl.reinit();
		cudaDeviceSynchronize();

		float elapsed_time;   // timing variables
		cudaEvent_t start_event, stop_event;
		cudaEventCreate(&start_event);
		cudaEventCreate(&stop_event);
		cudaEventRecord(start_event, 0);

		float ave_degree = (float) hg.nedges / (float) hg.nnodes;
		float ave_wt;
		{
			//find delta
			int a;
			cudaOccupancyMaxActiveBlocksPerMultiprocessor(&a, profiler_kernel, 1024, 0);
			int total_warp = other_num_tb * 1024 / 32;
			int warp_edge_interval = hg.nedges / (total_warp * I_TIME * N_TIME);
			float* host_bk_wt = (float*) malloc(other_num_tb * sizeof(float));
			float* bk_wt;
			cudaMalloc((void **) &bk_wt, other_num_tb * sizeof(float));
			profiler_kernel<<<other_num_tb, 1024>>>(gg, bk_wt, warp_edge_interval);
			cudaMemcpy(host_bk_wt, bk_wt, other_num_tb * sizeof(float), cudaMemcpyDeviceToHost);

			ave_wt = 0;
			for (int i = 0; i < other_num_tb; i++) {
				ave_wt += host_bk_wt[i];
			}
			ave_wt /= other_num_tb;
		}
		wl.set_param(ave_wt, ave_degree);
		gg_main_pipe_1_wrapper(hg, gg, start_node, num_tb, num_threads, wl, work_count);

		check_cuda(cudaEventRecord(stop_event, 0));
		check_cuda(cudaEventSynchronize(stop_event));
		check_cuda(cudaEventElapsedTime(&elapsed_time, start_event, stop_event));

		unsigned* work_count_host = (unsigned*) malloc(num_tb * num_threads * sizeof(unsigned));

		check_cuda(cudaMemcpy(work_count_host, work_count, num_tb * num_threads * sizeof(unsigned), cudaMemcpyDeviceToHost));
		unsigned long long total_work = 0;
		for (int i = 0; i < num_tb * num_threads; i++) {
			total_work += work_count_host[i];
		}

		agg_time += elapsed_time;
		agg_total_work += total_work;

		printf("%s Measured time for sample = %.3fs\n", hg.file_name, elapsed_time / 1000.0f);
		printf("total work is %llu\n", total_work);

	}

	float ave_time = agg_time / RUN_LOOP;
	long long unsigned ave_work = agg_total_work / RUN_LOOP;
	fprintf(d3, "%s %.3f %llu\n", hg.file_name, ave_time, ave_work);
	wl.free();
	cudaFree(work_count);
	fclose(d3);

//clean up
}

int main(int argc, char *argv[]) {
	if (argc == 1) {
		usage(argc, argv);
		exit(1);
	}
	parse_args(argc, argv);
	cudaSetDevice(CUDA_DEVICE);
	CSRGraphTy g, gg;
	g.read(INPUT);
	g.copy_to_gpu(gg);
	gg_main(g, gg);
	gg.copy_to_cpu(g);
	output(g, OUTPUT);

	return 0;
}

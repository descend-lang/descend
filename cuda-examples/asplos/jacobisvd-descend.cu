#include <cfloat>
#include <iostream>

#define BENCH
#include "descend.cuh"

// Added manually
__device__ static float eps() { return FLT_EPSILON; }

__device__ auto jacobiSVD(descend::f32 *const s_V, descend::f32 *const s_S,
                          descend::f32 *const s_acc1,
                          descend::f32 *const s_acc2, descend::f32 *const s_d)
    -> void {
  {
    {
      {

        if (((threadIdx.x - 0) < 9)) {
          {
            auto acc1 = 0.0f;
            for (std::size_t i = 0; (i < 9); i = (i + 1u)) {
              const auto val = s_S[(((threadIdx.y - 0) * 81) +
                                    (((threadIdx.x - 0) * 9) + i))];
              acc1 = (acc1 + (val * val));
              descend::f32 mat_elem;
              if ((threadIdx.x == (descend::u32)(i))) {
                mat_elem = 1.0f;
              } else {
                mat_elem = 0.0f;
              }

              s_V[(((threadIdx.y - 0) * 81) + (((threadIdx.x - 0) * 9) + i))] =
                  mat_elem;
            }

            s_d[(((threadIdx.y - 0) * 9) + (threadIdx.x - 0))] = acc1;
          }
        } else {
        }

        __syncthreads();
        for (std::size_t it = 0; (it < 30); it = (it + 1u)) {
          for (std::size_t i = 0; (i < 8); i = (i + 1u)) {
            for (std::size_t j = (i + 1); (j < 9); j = (j + 1u)) {
              const auto Si = (&s_S[(((threadIdx.y - 0) * 81) + (i * 9))]);
              const auto Sj = (&s_S[(((threadIdx.y - 0) * 81) + (j * 9))]);
              const auto Vi = (&s_V[(((threadIdx.y - 0) * 81) + (i * 9))]);
              const auto Vj = (&s_V[(((threadIdx.y - 0) * 81) + (j * 9))]);
              auto p = 0.0f;
              for (std::size_t k = 0; (k < 9); k = (k + 1u)) {
                p = (p + (Si[k] * Sj[k]));
              }

              const auto di = s_d[(((threadIdx.y - 0) * 9) + i)];
              const auto dj = s_d[(((threadIdx.y - 0) * 9) + j)];
              __syncthreads();
              auto c = 0.0f;
              auto s = 0.0f;
              auto t0 = 0.0f;
              auto t1 = 0.0f;
              const auto cond = (fabs(p) > ((9.0f * eps()) * sqrt((di * dj))));
              if (((threadIdx.x - 0) < 9)) {
                {
                  if (cond) {
                    const auto y = (di - dj);
                    const auto r = hypot((p * 2.0f), y);
                    const auto r2 = (r * 2.0f);
                    if ((y >= 0.0f)) {
                      c = sqrt(((r + y) / r2));
                      s = (p / (r2 * c));
                    } else {
                      s = sqrt(((r - y) / r2));
                      c = (p / (r2 * s));
                    }

                    t0 = ((c * Si[(threadIdx.x - 0)]) +
                          (s * Sj[(threadIdx.x - 0)]));
                    t1 = ((c * Sj[(threadIdx.x - 0)]) -
                          (s * Si[(threadIdx.x - 0)]));
                    Si[(threadIdx.x - 0)] = t0;
                    Sj[(threadIdx.x - 0)] = t1;
                    s_acc1[(((threadIdx.y - 0) * 16) +
                            (0 + (threadIdx.x - 0)))] = (t0 * t0);
                    s_acc2[(((threadIdx.y - 0) * 16) +
                            (0 + (threadIdx.x - 0)))] = (t1 * t1);
                  }
                }
              } else {
              }

              __syncthreads();
              if (cond) {
                auto a = 0.0f;
                auto b = 0.0f;
                for (std::size_t k = 0; (k < 9); k = (k + 1u)) {
                  a = (a + s_acc1[(((threadIdx.y - 0) * 16) + k)]);
                  b = (b + s_acc2[(((threadIdx.y - 0) * 16) + k)]);
                }

                s_d[(((threadIdx.y - 0) * 9) + i)] = a;
                s_d[(((threadIdx.y - 0) * 9) + j)] = b;
              }

              __syncthreads();
              if (cond) {
                if (((threadIdx.x - 0) < 9)) {
                  {
                    const auto t00 = ((Vi[(threadIdx.x - 0)] * c) +
                                      (Vj[(threadIdx.x - 0)] * s));
                    const auto t11 = ((Vj[(threadIdx.x - 0)] * c) -
                                      (Vi[(threadIdx.x - 0)] * s));
                    Vi[(threadIdx.x - 0)] = t00;
                    Vj[(threadIdx.x - 0)] = t11;
                  }
                } else {
                }
              }

              __syncthreads();
            }
          }
        }
      }
    }
  }
}

__global__ void wrapper_kernel(float * buffer) {
  __shared__ descend::f32 s_acc1[256];
  __shared__ descend::f32 s_acc2[256];
  __shared__ descend::f32 s_d[16*9];
  extern __shared__ descend::f32 sh[];

  for (size_t i = threadIdx.y * 16 + threadIdx.x; i < 32*81; i = i + 16*16) {
    sh[i] = buffer[i];
  }

  descend::f32 *s_V = sh;
  descend::f32 *s_S = sh + 16*81;
  jacobiSVD(s_V, s_S, s_acc1, s_acc2, s_d);

  for (size_t i = threadIdx.y * 16 + threadIdx.x; i < 32*81; i = i + 16*16) {
    buffer[i] = sh[i];
  }
}

void jacobiH(float *buffer, size_t N) {
    float * d_buffer;
    CHECK_CUDA_ERR(cudaMalloc(&d_buffer, sizeof(float) * N));
    CHECK_CUDA_ERR(cudaMemcpy(d_buffer, buffer, sizeof(float) * N, cudaMemcpyHostToDevice));

    // BENCHMARK
    descend::Timing timing{};
    timing.record_begin();
    wrapper_kernel<<<dim3(1,1), dim3(16,16), sizeof(float) * N>>>(d_buffer);
    timing.record_end();
    benchmark.current_run().insert_timing(timing);

    CHECK_CUDA_ERR(cudaMemcpy(buffer, d_buffer, sizeof(float) * N, cudaMemcpyDeviceToHost));
    cudaFree(d_buffer);
}

descend::Benchmark benchmark{descend::BenchConfig({"jacobisvd"})};
int main() {
    cudaError_t err;

    static constexpr std::size_t N = 32*81;
    float * buffer =  new float[N];

    std::iota(buffer, buffer + N, 1.0f);
    for (std::size_t iter = 0; iter < 100; iter++) {
        std::iota(buffer, buffer + N, 1.0f);

        jacobiH(buffer, N);
    }

    for (size_t i=0; i < N; i++)  {
        std::cout << buffer[i] << std::endl;
    }
    delete[] buffer;

    std::size_t size_in_mib = N * sizeof(float)/1024/1024;
    std::cout << "Input Size: " << size_in_mib << " MiB" << std::endl;
    std::cout << benchmark.to_csv();
    std::cout << "--------------" << std::endl;

    benchmark.reset();
}

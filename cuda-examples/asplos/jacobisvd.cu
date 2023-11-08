#include <cfloat>
#include <iostream>

#define BENCH
#include "descend.cuh"

template<typename T>
struct EPS {
    __device__ T eps() { return FLT_EPSILON; }
};

template<>
struct EPS<float> {
  __device__ static float eps() { return FLT_EPSILON; }
};

extern __shared__ float sh[];

template<typename T>
__device__ void JacobiSVD(int m, int n) {
    const int iterations = 30;

    int tid_x = threadIdx.x;
    int bsz_x = blockDim.x;
    int tid_y = threadIdx.y;
    // int gid_y = blockIdx.y * blockDim.y + tid_y;

    __shared__ T s_acc1[256];
    __shared__ T s_acc2[256];

    __shared__ T s_d[16 * 9];

    T* s_V = (T*)sh;
    T* s_S = (T*)sh + 16 * 81;

    int doff = tid_y * n;
    int soff = tid_y * 81;

    if (tid_x < n) {
        T acc1 = 0;
        for (int i = 0; i < m; i++) {
            int stid = soff + tid_x * m + i;
            T t      = s_S[stid];
            acc1 += t * t;
            s_V[stid] = (tid_x == i) ? 1 : 0;
        }
        s_d[doff + tid_x] = acc1;
    }
    __syncthreads();

    for (int it = 0; it < iterations; it++) {
        for (int i = 0; i < n - 1; i++) {
            for (int j = i + 1; j < n; j++) {
                T* Si = s_S + soff + i * m;
                T* Sj = s_S + soff + j * m;

                T* Vi = s_V + soff + i * n;
                T* Vj = s_V + soff + j * n;

                T p = (T)0;
                for (int k = 0; k < m; k++) p += Si[k] * Sj[k];

                T di = s_d[doff + i];
                T dj = s_d[doff + j];
                __syncthreads();

                T c = 0, s = 0;
                T t0 = 0, t1 = 0;
                int cond = (fabs(p) > m * EPS<T>::eps() * sqrt(di * dj));
                T a = 0, b = 0;

                if (cond) {
                    T y  = di - dj;
                    T r  = hypot(p * 2, y);
                    T r2 = r * 2;
                    if (y >= 0) {
                        c = sqrt((r + y) / r2);
                        s = p / (r2 * c);
                    } else {
                        s = sqrt((r - y) / r2);
                        c = p / (r2 * s);
                    }

                    for (int k = tid_x; k < m; k += bsz_x) {
                        t0                        = c * Si[k] + s * Sj[k];
                        t1                        = c * Sj[k] - s * Si[k];
                        Si[k]                     = t0;
                        Sj[k]                     = t1;
                        s_acc1[tid_y * bsz_x + k] = t0 * t0;
                        s_acc2[tid_y * bsz_x + k] = t1 * t1;
                    }
                }
                __syncthreads();

                if (cond) {
                    a = 0;
                    b = 0;
                    for (int k = 0; k < m; k++) {
                        a += s_acc1[tid_y * bsz_x + k];
                        b += s_acc2[tid_y * bsz_x + k];
                    }
                    s_d[doff + i] = a;
                    s_d[doff + j] = b;
                }
                __syncthreads();

                if (cond) {
                    for (int l = tid_x; l < n; l += bsz_x) {
                        T t0 = Vi[l] * c + Vj[l] * s;
                        T t1 = Vj[l] * c - Vi[l] * s;

                        Vi[l] = t0;
                        Vj[l] = t1;
                    }
                }
                __syncthreads();
            }
        }
    }
}

__global__ void wrapper_kernel(float * buffer) {
  for (size_t i = threadIdx.y * 16 + threadIdx.x; i < 32*81; i = i + 16*16) {
    sh[i] = buffer[i];
  }
  JacobiSVD<float>(9, 9);
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


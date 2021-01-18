#include <stdio.h>

#define CHECK_CUDA_ERR(err) { checkCudaErr((err), __FILE__, __LINE__); }
inline void checkCudaErr(cudaError_t err, const char *file, int line) {
  if (err != cudaSuccess) {
    fprintf(stderr, "Cuda Error: %s %s %d\n", cudaGetErrorString(err), file, line);
    exit(err);
  }
}

__global__
void inplace_vector_add_kernel_0(int *a_array, int *b_array) {
  int g_tid = blockIdx.x * blockDim.x + threadIdx.x;
  a_array[g_tid] = a_array[g_tid] + b_array[g_tid];
}

int * copyToGPU_ha_array(int *ha_array, int n) {
  int *a_array;
  size_t buffer_size = n*sizeof(int);
  CHECK_CUDA_ERR(cudaMalloc(&a_array, buffer_size));
  CHECK_CUDA_ERR(cudaMemcpy(a_array, ha_array, buffer_size, cudaMemcpyHostToDevice));
  return a_array;
}

int * copyToGPU_hb_array(int *hb_array, int n) {
  int *b_array;
  size_t buffer_size = n*sizeof(int);
  CHECK_CUDA_ERR(cudaMalloc(&b_array, buffer_size));
  CHECK_CUDA_ERR(cudaMemcpy(b_array, hb_array, buffer_size, cudaMemcpyHostToDevice));
  return b_array;
}

void inplace_vector_add_host(int *ha_array, int *hb_array, int n) {
  cudaSetDevice(0);
  int *a_array = copyToGPU_ha_array(ha_array, n);
  int *b_array = copyToGPU_hb_array(hb_array, n);
  inplace_vector_add_kernel_0<<<64, 1024>>>(a_array, b_array, n);
  CHECK_CUDA_ERR(cudaPeekAtLastError());
  // Necessary if no following blocking call to cudaMemcpy for example.
  // A cudaMemcpy should always exist if an At-Type value was created inside of
  // the descend function containing the par_for.
  // However, the At-Type value could also be passed to the function from the outside.
  // TODO Does that change anything?
  // CHECK_CUDA_ERR(cudaDeviceSynchronize())
    CHECK_CUDA_ERR(cudaMemcpy(ha_array, a_array, n*sizeof(int), cudaMemcpyDeviceToHost));
    CHECK_CUDA_ERR(cudaFree(a_array));
    CHECK_CUDA_ERR(cudaFree(b_array));
}

int main() {
  // Preamble to call of inplace_vector_add_host.
  // init ha_array, hb_array;
  // inplace_vector_add_host(ha_array, hb_array, n);
  exit(EXIT_SUCCESS);
  // free(ha_array);
  // free(hb_array);
} 

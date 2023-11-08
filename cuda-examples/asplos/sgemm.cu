// keplerBest kernel from RISE
// local size: (32, 8, 1)
// global size: (256, 128, 1)

#define BENCH
#include "../descend.cuh"

struct Record_64_float_128_float {
  float _fst[64];
  float _snd[128];
};


__global__ void foo(global float* restrict output,
         int N, int M, int K,
         const global float* restrict mat_a,
         const global float* restrict mat_b,
         const global float* restrict mat_c,
         local struct Record_64_float_128_float* restrict temp){
  /* Start of moved local vars */
  /* End of moved local vars */
  /* mapWorkGroup */
  for (int y_blockid_stride = blockIdx.y; y_blockid_stride < (M / 64); y_blockid_stride = 16 + y_blockid_stride) {
    /* mapWorkGroup */
    for (int x_blockid_stride = blockIdx.x; x_blockid_stride < (N / 128); x_blockid_stride = 8 + x_blockid_stride) {
      /* oclReduceSeq */
      {
        float accum[1024];
        /* mapLocal */
        /* unrolling loop of 1 */
        /* mapLocal */
        /* unrolling loop of 1 */
        /* mapSeq */
        /* unrolling loop of 8 */
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[32 * threadIdx.x] = 0.0f;
        accum[1 + (32 * threadIdx.x)] = 0.0f;
        accum[2 + (32 * threadIdx.x)] = 0.0f;
        accum[3 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[4 + (32 * threadIdx.x)] = 0.0f;
        accum[5 + (32 * threadIdx.x)] = 0.0f;
        accum[6 + (32 * threadIdx.x)] = 0.0f;
        accum[7 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[8 + (32 * threadIdx.x)] = 0.0f;
        accum[9 + (32 * threadIdx.x)] = 0.0f;
        accum[10 + (32 * threadIdx.x)] = 0.0f;
        accum[11 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[12 + (32 * threadIdx.x)] = 0.0f;
        accum[13 + (32 * threadIdx.x)] = 0.0f;
        accum[14 + (32 * threadIdx.x)] = 0.0f;
        accum[15 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[16 + (32 * threadIdx.x)] = 0.0f;
        accum[17 + (32 * threadIdx.x)] = 0.0f;
        accum[18 + (32 * threadIdx.x)] = 0.0f;
        accum[19 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[20 + (32 * threadIdx.x)] = 0.0f;
        accum[21 + (32 * threadIdx.x)] = 0.0f;
        accum[22 + (32 * threadIdx.x)] = 0.0f;
        accum[23 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[24 + (32 * threadIdx.x)] = 0.0f;
        accum[25 + (32 * threadIdx.x)] = 0.0f;
        accum[26 + (32 * threadIdx.x)] = 0.0f;
        accum[27 + (32 * threadIdx.x)] = 0.0f;
        /* mapSeq */
        /* unrolling loop of 4 */
        accum[28 + (32 * threadIdx.x)] = 0.0f;
        accum[29 + (32 * threadIdx.x)] = 0.0f;
        accum[30 + (32 * threadIdx.x)] = 0.0f;
        accum[31 + (32 * threadIdx.x)] = 0.0f;
        for (int loop_tiles_i = 0; loop_tiles_i < (K / 8); loop_tiles_i = 1 + loop_tiles_i) {
          /* mapLocal */
          /* iteration count is exactly 1, no loop emitted */
          int local_y_id = threadIdx.y;
          /* mapLocal */
          for (int loop_cpy_tile_a_xstride_i = threadIdx.x; loop_cpy_tile_a_xstride_i < 64; loop_cpy_tile_a_xstride_i = 32 + loop_cpy_tile_a_xstride_i) {
            // a_tile[(((threadIdx.y - 0) * (32 * 2)) + ((i * 32) + (threadIdx.x - 0)))] =
            //      a_transp_mat[((((tnum * 8) + (threadIdx.y - 0)) * m) +
            //          ((((wgY * 16) + (blockIdx.y - 0)) * 64) + ((i * 32) + (threadIdx.x - 0))))];
            temp[local_y_id]._fst[loop_cpy_tile_a_xstride_i] = mat_a[loop_cpy_tile_a_xstride_i + ((8 * loop_tiles_i) * M) + (64 * y_blockid_stride) + (local_y_id * M)];
          }
          
          /* mapLocal */
          for (int l_id_1318 = threadIdx.x; l_id_1318 < 128; l_id_1318 = 32 + l_id_1318) {
            // b_tile[(((threadIdx.y - 0) * (32 * 4)) + ((i * 32) + (threadIdx.x - 0)))] =
            //      b_mat[((((tnum * 8) + (threadIdx.y - 0)) * n) +
            //          ((((wgX * 8) + (blockIdx.x - 0)) * 128) + ((i * 32) + (threadIdx.x - 0))))];
            temp[local_y_id]._snd[l_id_1318] = mat_b[((l_id_1318 + ((8 * loop_tiles_i) * N)) + (128 * x_blockid_stride)) + (local_y_id * N)];
          }
          
          barrier(CLK_LOCAL_MEM_FENCE);
          /* mapLocal */
          /* unrolling loop of 1 */
          /* mapLocal */
          /* unrolling loop of 1 */
          /* oclReduceSeq */
          {
            float accum_cpy[32];
            /* mapSeq */
            /* unrolling loop of 8 */
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[0] = accum[32 * threadIdx.x];
            accum_cpy[1] = accum[1 + (32 * threadIdx.x)];
            accum_cpy[2] = accum[2 + (32 * threadIdx.x)];
            accum_cpy[3] = accum[3 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[4] = accum[4 + (32 * threadIdx.x)];
            accum_cpy[5] = accum[5 + (32 * threadIdx.x)];
            accum_cpy[6] = accum[6 + (32 * threadIdx.x)];
            accum_cpy[7] = accum[7 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[8] = accum[8 + (32 * threadIdx.x)];
            accum_cpy[9] = accum[9 + (32 * threadIdx.x)];
            accum_cpy[10] = accum[10 + (32 * threadIdx.x)];
            accum_cpy[11] = accum[11 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[12] = accum[12 + (32 * threadIdx.x)];
            accum_cpy[13] = accum[13 + (32 * threadIdx.x)];
            accum_cpy[14] = accum[14 + (32 * threadIdx.x)];
            accum_cpy[15] = accum[15 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[16] = accum[16 + (32 * threadIdx.x)];
            accum_cpy[17] = accum[17 + (32 * threadIdx.x)];
            accum_cpy[18] = accum[18 + (32 * threadIdx.x)];
            accum_cpy[19] = accum[19 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[20] = accum[20 + (32 * threadIdx.x)];
            accum_cpy[21] = accum[21 + (32 * threadIdx.x)];
            accum_cpy[22] = accum[22 + (32 * threadIdx.x)];
            accum_cpy[23] = accum[23 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[24] = accum[24 + (32 * threadIdx.x)];
            accum_cpy[25] = accum[25 + (32 * threadIdx.x)];
            accum_cpy[26] = accum[26 + (32 * threadIdx.x)];
            accum_cpy[27] = accum[27 + (32 * threadIdx.x)];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum_cpy[28] = accum[28 + (32 * threadIdx.x)];
            accum_cpy[29] = accum[29 + (32 * threadIdx.x)];
            accum_cpy[30] = accum[30 + (32 * threadIdx.x)];
            accum_cpy[31] = accum[31 + (32 * threadIdx.x)];
            for (int i_1319 = 0; i_1319 < 8; i_1319 = 1 + i_1319) {
              {
                float temp1_regs[8];
                /* mapSeq */
                /* unrolling loop of 8 */
                temp1_regs[0] = temp[i_1319]._fst[8 * threadIdx.y];
                temp1_regs[1] = temp[i_1319]._fst[1 + (8 * threadIdx.y)];
                temp1_regs[2] = temp[i_1319]._fst[2 + (8 * threadIdx.y)];
                temp1_regs[3] = temp[i_1319]._fst[3 + (8 * threadIdx.y)];
                temp1_regs[4] = temp[i_1319]._fst[4 + (8 * threadIdx.y)];
                temp1_regs[5] = temp[i_1319]._fst[5 + (8 * threadIdx.y)];
                temp1_regs[6] = temp[i_1319]._fst[6 + (8 * threadIdx.y)];
                temp1_regs[7] = temp[i_1319]._fst[7 + (8 * threadIdx.y)];
                {
                  float temp2_regs[4];
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  temp2_regs[0] = temp[i_1319]._snd[threadIdx.x];
                  temp2_regs[1] = temp[i_1319]._snd[32 + threadIdx.x];
                  temp2_regs[2] = temp[i_1319]._snd[64 + threadIdx.x];
                  temp2_regs[3] = temp[i_1319]._snd[96 + threadIdx.x];
                  /* mapSeq */
                  /* unrolling loop of 8 */
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[0] = accum_cpy[0] + (temp1_regs[0] * temp2_regs[0]);
                  accum_cpy[1] = accum_cpy[1] + (temp1_regs[0] * temp2_regs[1]);
                  accum_cpy[2] = accum_cpy[2] + (temp1_regs[0] * temp2_regs[2]);
                  accum_cpy[3] = accum_cpy[3] + (temp1_regs[0] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[4] = accum_cpy[4] + (temp1_regs[1] * temp2_regs[0]);
                  accum_cpy[5] = accum_cpy[5] + (temp1_regs[1] * temp2_regs[1]);
                  accum_cpy[6] = accum_cpy[6] + (temp1_regs[1] * temp2_regs[2]);
                  accum_cpy[7] = accum_cpy[7] + (temp1_regs[1] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[8] = accum_cpy[8] + (temp1_regs[2] * temp2_regs[0]);
                  accum_cpy[9] = accum_cpy[9] + (temp1_regs[2] * temp2_regs[1]);
                  accum_cpy[10] = accum_cpy[10] + (temp1_regs[2] * temp2_regs[2]);
                  accum_cpy[11] = accum_cpy[11] + (temp1_regs[2] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[12] = accum_cpy[12] + (temp1_regs[3] * temp2_regs[0]);
                  accum_cpy[13] = accum_cpy[13] + (temp1_regs[3] * temp2_regs[1]);
                  accum_cpy[14] = accum_cpy[14] + (temp1_regs[3] * temp2_regs[2]);
                  accum_cpy[15] = accum_cpy[15] + (temp1_regs[3] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[16] = accum_cpy[16] + (temp1_regs[4] * temp2_regs[0]);
                  accum_cpy[17] = accum_cpy[17] + (temp1_regs[4] * temp2_regs[1]);
                  accum_cpy[18] = accum_cpy[18] + (temp1_regs[4] * temp2_regs[2]);
                  accum_cpy[19] = accum_cpy[19] + (temp1_regs[4] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[20] = accum_cpy[20] + (temp1_regs[5] * temp2_regs[0]);
                  accum_cpy[21] = accum_cpy[21] + (temp1_regs[5] * temp2_regs[1]);
                  accum_cpy[22] = accum_cpy[22] + (temp1_regs[5] * temp2_regs[2]);
                  accum_cpy[23] = accum_cpy[23] + (temp1_regs[5] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[24] = accum_cpy[24] + (temp1_regs[6] * temp2_regs[0]);
                  accum_cpy[25] = accum_cpy[25] + (temp1_regs[6] * temp2_regs[1]);
                  accum_cpy[26] = accum_cpy[26] + (temp1_regs[6] * temp2_regs[2]);
                  accum_cpy[27] = accum_cpy[27] + (temp1_regs[6] * temp2_regs[3]);
                  /* mapSeq */
                  /* unrolling loop of 4 */
                  accum_cpy[28] = accum_cpy[28] + (temp1_regs[7] * temp2_regs[0]);
                  accum_cpy[29] = accum_cpy[29] + (temp1_regs[7] * temp2_regs[1]);
                  accum_cpy[30] = accum_cpy[30] + (temp1_regs[7] * temp2_regs[2]);
                  accum_cpy[31] = accum_cpy[31] + (temp1_regs[7] * temp2_regs[3]);
                }
                
              }
              
            }
            
            /* mapSeq */
            /* unrolling loop of 8 */
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[32 * threadIdx.x] = accum_cpy[0];
            accum[1 + (32 * threadIdx.x)] = accum_cpy[1];
            accum[2 + (32 * threadIdx.x)] = accum_cpy[2];
            accum[3 + (32 * threadIdx.x)] = accum_cpy[3];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[4 + (32 * threadIdx.x)] = accum_cpy[4];
            accum[5 + (32 * threadIdx.x)] = accum_cpy[5];
            accum[6 + (32 * threadIdx.x)] = accum_cpy[6];
            accum[7 + (32 * threadIdx.x)] = accum_cpy[7];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[8 + (32 * threadIdx.x)] = accum_cpy[8];
            accum[9 + (32 * threadIdx.x)] = accum_cpy[9];
            accum[10 + (32 * threadIdx.x)] = accum_cpy[10];
            accum[11 + (32 * threadIdx.x)] = accum_cpy[11];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[12 + (32 * threadIdx.x)] = accum_cpy[12];
            accum[13 + (32 * threadIdx.x)] = accum_cpy[13];
            accum[14 + (32 * threadIdx.x)] = accum_cpy[14];
            accum[15 + (32 * threadIdx.x)] = accum_cpy[15];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[16 + (32 * threadIdx.x)] = accum_cpy[16];
            accum[17 + (32 * threadIdx.x)] = accum_cpy[17];
            accum[18 + (32 * threadIdx.x)] = accum_cpy[18];
            accum[19 + (32 * threadIdx.x)] = accum_cpy[19];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[20 + (32 * threadIdx.x)] = accum_cpy[20];
            accum[21 + (32 * threadIdx.x)] = accum_cpy[21];
            accum[22 + (32 * threadIdx.x)] = accum_cpy[22];
            accum[23 + (32 * threadIdx.x)] = accum_cpy[23];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[24 + (32 * threadIdx.x)] = accum_cpy[24];
            accum[25 + (32 * threadIdx.x)] = accum_cpy[25];
            accum[26 + (32 * threadIdx.x)] = accum_cpy[26];
            accum[27 + (32 * threadIdx.x)] = accum_cpy[27];
            /* mapSeq */
            /* unrolling loop of 4 */
            accum[28 + (32 * threadIdx.x)] = accum_cpy[28];
            accum[29 + (32 * threadIdx.x)] = accum_cpy[29];
            accum[30 + (32 * threadIdx.x)] = accum_cpy[30];
            accum[31 + (32 * threadIdx.x)] = accum_cpy[31];
          }
          
          barrier(CLK_LOCAL_MEM_FENCE);
        }
        
        /* mapLocal */
        /* unrolling loop of 1 */
        /* mapLocal */
        /* unrolling loop of 1 */
        /* mapSeq */
        /* unrolling loop of 8 */
        /* mapSeq */
        /* unrolling loop of 4 */
        output[(((0 + (8 * N) * threadIdx.y) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[0 + (32 * threadIdx.x)] * alpha) + (mat_c[((((8 * N) * threadIdx.y) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[(((32 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[1 + (32 * threadIdx.x)] * alpha) + (mat_c[(((32 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[(((64 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[2 + (32 * threadIdx.x)] * alpha) + (mat_c[(((64 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[(((96 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[3 + (32 * threadIdx.x)] * alpha) + (mat_c[(((96 + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[(((N + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[4 + (32 * threadIdx.x)] * alpha) + (mat_c[(((N + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[5 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[6 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] =
                (accum[7 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((2 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[8 + (32 * threadIdx.x)] * alpha) + (mat_c[((((2 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[9 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[10 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[11 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (2 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((3 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[12 + (32 * threadIdx.x)] * alpha) + (mat_c[((((3 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[13 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[14 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[15 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (3 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((4 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[16 + (32 * threadIdx.x)] * alpha) + (mat_c[((((4 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[17 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[18 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[19 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (4 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((5 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[20 + (32 * threadIdx.x)] * alpha) + (mat_c[((((5 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[21 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[22 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[23 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (5 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((6 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[24 + (32 * threadIdx.x)] * alpha) + (mat_c[((((6 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[25 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[26 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[27 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (6 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        /* mapSeq */
        /* unrolling loop of 4 */
        output[((((7 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[28 + (32 * threadIdx.x)] * alpha) + (mat_c[((((7 * N) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((32 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[29 + (32 * threadIdx.x)] * alpha) + (mat_c[((((32 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((64 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[30 + (32 * threadIdx.x)] * alpha) + (mat_c[((((64 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
        output[((((96 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] = (accum[31 + (32 * threadIdx.x)] * alpha) + (mat_c[((((96 + (7 * N)) + ((8 * N) * threadIdx.y)) + ((64 * N) * y_blockid_stride)) + (128 * x_blockid_stride)) + threadIdx.x] * beta);
      }
      
    }
    
  }
  
}

template<std::size_t m, std::size_t n, std::size_t k>
auto cpu_sgemm(
        descend::i32 * const hout_mat,
        descend::i32 const * const ha_mat_transp, // [[i32; m]; k]
        descend::i32 const * const hb_mat, // [[i32; n]; k]
        descend::i32 const * const hc_mat, // [[i32; n]; m]
        descend::i32 alpha, descend::i32 beta) {
    for (int j = 0; j < k; ++j) {
        for (int i = 0; i < m; ++i)
            for (int l = 0; l < n; ++l)
                hout_mat[i * n + l] += ha_mat_transp[j * m + i] * hb_mat[j * n + l];
    }

    for (int i = 0; i < m; ++i)
        for (int l = 0; l < n; ++l)
            hout_mat[i*n + l] = alpha * hout_mat[i*n+l] + beta * hc_mat[i*n + l];
}

descend::Benchmark benchmark{descend::BenchConfig({"sgemm"})};
auto main() -> int {
    static constexpr std::size_t m[] = {8192, 8192, 16384};
    static constexpr auto n = 8192;
    static constexpr std::size_t k[] = {4096, 8192, 8192};

    static_for<0, 3>([](auto i) {
        const auto ha_mat_transp = new descend::i32[k[i]*m[i]];
        const auto hb_mat = new descend::i32[k[i]*n];
        const auto hc_mat = new descend::i32[m[i]*n];
        auto hout_mat = new descend::i32[m[i]*n];
        std::fill(ha_mat_transp, ha_mat_transp + k[i]*m[i], 1);
        std::fill(hb_mat, hb_mat + k[i]*n, 1);
        std::fill(hc_mat, hc_mat + m[i]*n, 1);

        std::cout << "Footprint: " << (k[i]*m[i] + k[i]*n + 2*m[i]*n)*sizeof(int)/1024/1024 << " MiB" << std::endl;
        auto gold = new descend::i32[m[i]*n];
        std::cout << "Compute gold..." << std::endl;
        cpu_sgemm<m[i], n, k[i]>(gold, ha_mat_transp, hb_mat, hc_mat, 1, 1);
        std::cout << "Gold computed. Starting measurement ..." << std::endl;

        for (std::size_t iter = 0; iter < 100; iter++) {
            std::fill(hout_mat, hout_mat + m[i]*n, 0);

            sgemm<m[i], n, k[i]>(hout_mat, n, m[i], k[i], ha_mat_transp, hb_mat, hc_mat);

            for (size_t j = 0; j < m[i]*n; j++) {
                if (gold[j] != hout_mat[j]) {
                    std::cout << "Error at " << j << ". Expected: " << gold[j] << " but found " << hout_mat[j] << "." << std::endl;
                    exit(EXIT_FAILURE);
                }
            }
        }
        delete[] gold;
        delete[] ha_mat_transp;
        delete[] hb_mat;
        delete[] hc_mat;
        delete[] hout_mat;

        std::cout << "Input sizes: m =" << m[i] << ", n = " << n << ", k = " << k[i] << std::endl;
        std::cout << benchmark.to_csv();

        benchmark.reset();
    });

    exit(EXIT_SUCCESS);
}

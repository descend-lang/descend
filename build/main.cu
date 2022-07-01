#include "output.cu"
#include "params.cuh"

    
int main() {
  const size_t items_per_thread = ITEMS_PER_THREAD;
  const size_t size_block = THREAD_PER_BLOCKS;
  const size_t items_per_block = items_per_thread * size_block;
  const size_t size_grid = BLOCKS_PER_GRID;
  const size_t items_per_grid = items_per_block * size_grid;
  int* ha_array = (int *) malloc(sizeof(int) * items_per_grid);
  int* flags = (int *) malloc(sizeof(int) * size_grid);
  int* aggs = (int *) malloc(sizeof(int) * size_grid);
  int* prefixs = (int *) malloc(sizeof(int) * size_grid);

  int* gold = (int *) malloc(sizeof(int) * items_per_grid);

  for (int i=0; i < items_per_grid; i++) {
    ha_array[i] = i % 30 + 1;
    gold[i] = ha_array[i];
  }

  for (int i = 1; i < items_per_grid; i++) {
    gold[i] += gold[i-1];
  }

  for (int i = 0; i < size_grid; i++) {
    flags[i] = 0;
  }

  prefix_scan<size_grid, size_block, items_per_thread>(ha_array, flags, aggs, prefixs);
  //prefix_scan(ha_array, flags, aggs, prefixs);

  // for (int i=0; i < items_per_grid; i++) {
  for (int i = 0; i < size_grid; i++) {
    printf("Index %d, Flag %d, Agg %d, prefix %d\n", i, flags[i], aggs[i], prefixs[i]);
  }
  for (int i=0; i < size_grid; i++) {
    if (gold[i] != ha_array[i]) {
      printf("bad value at %d, gold: %d, actual value %d\n", i, gold[i], ha_array[i]);
    }
  }

  free(ha_array);
  free(flags);
  free(aggs);
  free(prefixs);
}

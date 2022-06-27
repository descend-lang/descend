#include "output.cu"

    
int main() {
  size_t items_per_thread =  2;
  size_t size_block = 1024;
  size_t items_per_block = items_per_thread * size_block;
  size_t size_grid = 64;
  size_t items_per_grid = items_per_block * size_grid;
  int* ha_array = (int *) malloc(sizeof(int) * items_per_grid);
  int* flags = (int *) malloc(sizeof(int) * size_grid);
  int* aggs = (int *) malloc(sizeof(int) * size_grid);
  int* prefixs = (int *) malloc(sizeof(int) * size_grid);

  int* gold = (int *) malloc(sizeof(int) * items_per_grid);

  for (int i=0; i < items_per_grid; i++) {
    ha_array[i] = 2;
    gold[i] = ha_array[i];
  }

  for (int i = 1; i < items_per_grid; i++) {
    gold[i] += gold[i-1];
  }

  for (int i = 0; i < 64; i++) {
    flags[i] = 0;
  }

  prefix_scan(ha_array, flags, aggs, prefixs);

  for (int i=0; i < 2100; i++) {
    if (gold[i] != ha_array[i]) {
      printf("bad value at %d, gold: %d, actual value %d\n", i, gold[i], ha_array[i]);
    }
  }

  free(ha_array);
  free(flags);
  free(aggs);
  free(prefixs);
}



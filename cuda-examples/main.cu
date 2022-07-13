//#define BENCH

#include "output.cu"
#include "params.cuh"

// descend::Benchmark benchmark{descend::BenchConfig({1})};
    
int main() {
  const size_t items_per_thread = ITEMS_PER_THREAD;
  const size_t size_block = THREAD_PER_BLOCKS;
  const size_t items_per_block = items_per_thread * size_block;
  const size_t size_grid = BLOCKS_PER_GRID;
  const size_t items_per_grid = items_per_block * size_grid;

  for (int j = 0; j < 500; j++) {

    int* ha_array = (int *) malloc(sizeof(int) * items_per_grid);
    int* ha_init_array = (int *) malloc(sizeof(int) * items_per_grid);
    int* flags = (int *) malloc(sizeof(int) * size_grid);
    int* aggs = (int *) malloc(sizeof(int) * size_grid);
    int* prefixs = (int *) malloc(sizeof(int) * size_grid);
    int* gold = (int *) malloc(sizeof(int) * items_per_grid);
    for (int i=0; i < items_per_grid; i++) {
      ha_init_array[i] = i % 30 + 1;
      gold[i] = ha_init_array[i];
    }
    for (int i = 1; i < items_per_grid; i++) {
      gold[i] += gold[i-1];
    }
    // memccpy(ha_array, ha_init_array, 1, sizeof(int) * items_per_grid);
    for (int i=0; i < items_per_grid; i++) {
      ha_array[i] = i % 30 + 1;
    }

    memset(flags, 0, size_grid * sizeof(int));
    memset(aggs, 0, size_grid * sizeof(int));
    memset(prefixs, 0, size_grid * sizeof(int));

    prefix_scan<size_grid, size_block, items_per_thread>(ha_array, flags, aggs, prefixs);
    //prefix_scan(ha_array, flags, aggs, prefixs);

    // for (int i=0; i < items_per_grid; i++) {
    // for (int i = 0; i < size_grid; i++) {
    //   printf("Index %d, Flag %d, Agg %d, prefix %d\n", i, flags[i], aggs[i], prefixs[i]);
    // }
    printf("Execution %i\n", j);

    for (int i=0; i < items_per_grid; i++) {
      if (gold[i] != ha_array[i]) {
        printf("bad value at %d, gold: %d, actual value %d\n", i, gold[i], ha_array[i]);
        break;
      }
    }

    free(ha_array);
    free(flags);
    free(aggs);
    free(prefixs);
  }
  // std::cout << benchmark.to_csv();
}

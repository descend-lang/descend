#include "output.cu"

    
int main() {
  int size = 1024 * 2;
  int* ha_array = (int *) malloc(sizeof(int) * 64 * size);
  int* flags = (int *) malloc(sizeof(int) * 64);
  int* aggs = (int *) malloc(sizeof(int) * 64);
  int* prefixs = (int *) malloc(sizeof(int) * 64);

  for (int i=0; i < 64 * size; i++) {
    ha_array[i] = 2;
  }

  for (int i = 0; i < 64; i++) {
    flags[i] = 0;
  }

  prefix_scan(ha_array, flags, aggs, prefixs);

  for (int i=0; i < 4024; i++) {
    printf("%d\n", ha_array[i]);
  }

  free(ha_array);
  free(flags);
  free(aggs);
  free(prefixs);
}



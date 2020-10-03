#include <stdlib.h>
#include <stdint.h>

/* Add two numbers using a while loop that repeatedly increments */
int64_t add_loop (int64_t x, int64_t y) {
  uint64_t ret = x;
  for (uint64_t i = y; i > 0; -- i) {
    ret++;
  }
  return ret;
}

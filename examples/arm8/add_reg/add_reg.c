#include <stdint.h>

int64_t add_reg(int64_t x, int64_t y) {
  int64_t lx = x;
  int64_t ly = y;
  while (lx > 0) {
    ly += 1;
    lx -= 1;
  }
  return ly;
}

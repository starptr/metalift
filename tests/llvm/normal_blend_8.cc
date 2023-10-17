#include "list.h"

int mul8x8div255(int a, int b) {
  return a * b / 255;
}

std::vector<int> normal_blend_8(std::vector<int> base, std::vector<int> active, int opacity) 
{
  std::vector<int> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(mul8x8div255(opacity, active[i]) + mul8x8div255(255 - opacity, base[i]));

  return out;
}
#include <math.h>
#define TRUE 1
#define FALSE 0

float ex6(float v, float w, float r) {
  return (((3.0f + (2.0f / (r * r))) - (((0.125f * (3.0f - (2.001f * v))) * (((w * w) * r) * r)) / (1.0f - v))) - 4.5f);
}


double foo(double x) {
  double y = 0.0;
  for (int i = 0; i < 10; i++) {
    y = y + x;
  }

  return y; // Returning sum to avoid x and y being optimized away.
}

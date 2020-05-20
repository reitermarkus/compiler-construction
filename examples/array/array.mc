int main() {
  int[2] x;
  int y;
  y = 0;

  x[y] = 1;
  x[1] = 2;

  return 2 * x[0] - x[1];
}

int main() {
  int[2] x;
  int y;
  y = 0;

  int q;
  q = 2;

  int z;
  z = 3;

  x[y] = 4;
  x[1] = 2;

  return (x[0] * x[1] * q * z)- (y + z);
}

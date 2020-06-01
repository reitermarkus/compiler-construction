int main() {
  int y;
  y = 2;

  if ((y > 4) || (y < 4)) {
    y = 0;
  } else {
    y = 1;
    return 1;
  }

  return 3;
}

int main() {
  print("Enter two integers:");
  print_nl();

  int i1;
  i1 = read_int();

  int i2;
  i2 = read_int();

  int i;
  i = i1 + i2;

  print_int(i);
  print_nl();

  print_nl();

  print("Enter two floats:");
  print_nl();

  float f1;
  f1 = read_float();

  float f2;
  f2 = read_float();

  float f;
  f = f1 + f2;

  print_float(f);
  print_nl();

  return 0;
}

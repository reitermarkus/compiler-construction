void swap(int[4] arr, int i, int j){
  int tmp;
  tmp = arr[i];
  arr[i] = arr[j];
  arr[j] = tmp;
}

void print_array(int[4] arr, int arr_size){
  int i;
  i = 0;
  while(i < arr_size){
    print_int(arr[i]);
    print(" ");
    i = i+1;
  }
  print_nl();
}

int main(){
    int arr_size;
    arr_size = 4;

    int[4] arr;

    arr[0] = 10;
    arr[1] = 9;
    arr[2] = 8;
    arr[3] = 7;

    print("input array: ");
    print_array(arr, arr_size);

    swap(arr, 0, arr_size-1);

    print("output array: ");
    print_array(arr, arr_size);

    return 0;
}

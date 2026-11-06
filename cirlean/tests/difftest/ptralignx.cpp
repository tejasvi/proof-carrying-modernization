// Pointer conversions and alignment in C++ ([expr.static.cast]p13: a pointer converted to a pointer to an object type
// that it is not correctly aligned for has an unspecified value; not undefined, unlike C's); run with
// CASES=ptralign_cases.txt, which describes the cases.

// an int pointer one byte into an int array, by reinterpret_cast, not used
int x_misaligned_int(int k) {
  int a[2] = {1, 2};
  int *p = reinterpret_cast<int *>(reinterpret_cast<char *>(a) + 1 + k);
  return p != nullptr;
}

// the same through void * and static_cast
int x_misaligned_static(int k) {
  int a[2] = {1, 2};
  void *v = reinterpret_cast<char *>(a) + 1 + k;
  int *p = static_cast<int *>(v);
  return p != nullptr;
}

// an aligned conversion, used
int x_aligned_int(int k) {
  int a[2] = {1, 2 + k};
  int *p = reinterpret_cast<int *>(reinterpret_cast<char *>(a) + 4);
  return *p;
}

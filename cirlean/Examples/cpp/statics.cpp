// A function that writes a function-local static array (and returns a
// pointer into it), as re_compile in tiny-regex-c does.
extern "C" {
int *bump(int k) {
  static int counter[4];
  counter[k] = counter[k] + 1;
  return &counter[k];
}
}

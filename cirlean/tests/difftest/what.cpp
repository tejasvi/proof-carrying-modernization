// what() of std::exception and std::bad_alloc (run with CASES=what_cases.txt):
// fixed strings, the same in libc++ and libstdc++ ("std::exception",
// "std::bad_alloc"). The calls here are direct, or virtual through a class
// derived in the program (whose vtable is in the module); the vtable of
// std::exception itself is the library's. Expected result (labelled per case
// in the cases file): MATCH everywhere.
#include <cstring>
#include <exception>
#include <new>

struct MyError : std::exception {
  int code;
  explicit MyError(int c) : code(c) {}
};

int t_what_exception(int n) {
  std::exception e;
  return (int)std::strlen(e.what()) * 10 + n;
}

int t_what_text(int n) {
  std::exception e;
  return std::strcmp(e.what(), "std::exception") == 0 ? n : -n;
}

int t_what_derived(int n) {
  MyError e(n);
  const std::exception &r = e;
  return std::strcmp(r.what(), "std::exception") == 0 ? e.code : -1;
}

int t_what_bad_alloc(int n) {
  std::bad_alloc b;
  return std::strcmp(b.what(), "std::bad_alloc") == 0 ? n + 1 : -1;
}

int t_what_thrown(int n) {
  try {
    throw MyError(n);
  } catch (const MyError &e) {
    return e.what()[5] + e.code;
  }
  return -1;
}

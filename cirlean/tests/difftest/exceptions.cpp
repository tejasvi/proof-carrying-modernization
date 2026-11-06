// try/catch.
struct Err { int code; };

static int may_throw(int x) {
  if (x < 0) throw Err{x};
  if (x == 0) throw 42;
  return x * 2;
}

int t_catch_class(int x) {
  try {
    return may_throw(x);
  } catch (const Err &e) {
    return e.code - 1000;
  } catch (int v) {
    return v;
  }
}

int t_catch_all(int x) {
  int r = 5;
  try {
    r = may_throw(x);
  } catch (...) {
    r = -1;
  }
  return r;
}

int t_nested_try(int x) {
  int r = 0;
  try {
    try {
      if (x > 5) throw 1;
      r += 10;
    } catch (int) {
      r += 100;
      if (x > 8) throw 2;
    }
    r += 1000;
  } catch (int v) {
    r += v * 10000;
  }
  return r;
}

int t_throw_out(int x) {
  if (x > 3) throw 7;
  return x;
}

// throw; (run with CASES=rethrow_cases.txt): in a catch handler, the exception
// being handled propagates again, the same object. Expected result (labelled
// per case in the cases file): MATCH on the t_* cases; UB on u_rethrow_helper,
// a throw; in a function called from a handler (the current exception is known
// only inside a handler's own code).

struct E {
  int v;
};

int t_rethrow(int n) {
  try {
    try {
      throw E{n};
    } catch (E &e) {
      e.v += 1;
      throw;
    }
  } catch (E &e) {
    return e.v;
  }
  return -1;
}

int t_rethrow_all(int n) {
  try {
    try {
      throw n * 2;
    } catch (...) {
      throw;
    }
  } catch (int x) {
    return x + 1;
  }
  return -1;
}

int t_rethrow_same(int n) {
  try {
    throw E{n};
  } catch (E &e) {
    try {
      throw;
    } catch (E &f) {
      return &e == &f ? f.v : -2;
    }
  }
  return -1;
}

struct Guard {
  int *p;
  ~Guard() { *p += 10; }
};

int t_rethrow_cleanup(int n) {
  int k = 0;
  try {
    try {
      throw E{n};
    } catch (E &) {
      Guard g{&k};
      throw;
    }
  } catch (E &e) {
    return e.v + k;
  }
  return -1;
}

static void helper() {
  throw;
}

int u_rethrow_helper(int n) {
  try {
    try {
      throw E{n};
    } catch (E &) {
      helper();
    }
  } catch (E &e) {
    return e.v;
  }
  return -1;
}

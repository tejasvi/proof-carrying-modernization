// fflush (run with CASES=fflush_cases.txt): the output is not modelled (no
// buffers), so fflush has nothing to write and returns 0, for stdout, stderr
// and a null pointer (all streams). Expected result (labelled per case in the
// cases file): MATCH everywhere.
#include <cstdio>

int t_fflush_stdout(int n) {
  return fflush(stdout) + n;
}

int t_fflush_streams(int n) {
  int r = fflush(stdout);
  r = r * 2 + fflush(stderr);
  r = r * 2 + fflush(nullptr);
  return r * 100 + n;
}

int t_fflush_loop(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) s += fflush(stdout) == 0;
  return s;
}

/* C, not C++ (run with MODE=status CASES=retval_cases.txt): reaching the
   closing brace of a non-void function is undefined only if the caller uses
   the value (C11 6.9.1p12; in C++ it is undefined in itself, and CIRGen puts
   a trap there). Expected result, labelled per case in the cases file: MATCH
   where the value is discarded or was returned; UB from cirrun where the
   caller stores, adds, compares, tests, passes on or returns a missing value
   (native runs return whatever the register holds). */

/* a value only for k > 100 */
int maybe(int k) {
  if (k > 100)
    return k - 100;
}

/* a value only when the loop finds 7 */
int find7(int k) {
  for (int i = 0; i < k; i++)
    if (i == 7)
      return i;
}

double maybe_d(int k) {
  if (k > 0)
    return 1.5;
}

char *maybe_p(int k) {
  if (k > 0)
    return "p";
}

static int counter;

/* a void function reaching its closing brace */
void bump(int k) {
  if (k > 0)
    counter += k;
}

int id(int v) { return v; }

int t_unused(int k) {
  maybe(k);
  return 7;
}

int t_present(int k) { return maybe(k + 200); }

int t_stored(int k) {
  int x = maybe(k);
  (void)x;
  return 5;
}

int t_added(int k) { return maybe(k) + 1; }

int t_compared(int k) {
  if (maybe(k) == 0)
    return 1;
  return 2;
}

int t_branch(int k) { return maybe(k) ? 3 : 4; }

int t_passed(int k) { return id(maybe(k)); }

int t_returned(int k) { return maybe(k); }

int t_loop_unused(int k) {
  find7(k);
  return 8;
}

int t_loop_used(int k) { return find7(k); }

int t_double_unused(int k) {
  maybe_d(k);
  return 11;
}

int t_double_used(int k) { return maybe_d(k) > 1.0; }

int t_ptr_unused(int k) {
  maybe_p(k);
  return 12;
}

int t_void(int k) {
  counter = 1;
  bump(k);
  return counter;
}

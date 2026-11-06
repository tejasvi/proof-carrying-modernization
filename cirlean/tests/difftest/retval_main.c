/* C (run with MODE=status CASES=retval_cases.txt): main reaching its closing
   brace returns 0 (C11 5.1.2.2.3); CIRGen stores 0 into its return slot at
   entry. It discards the missing value of a function that reaches its own
   closing brace (C11 6.9.1p12). Expected result: MATCH, status 0. */

static int maybe(int k) {
  if (k > 100)
    return k;
}

int main(void) {
  int s = 0;
  for (int i = 0; i < 3; i++)
    s += i;
  maybe(s);
}

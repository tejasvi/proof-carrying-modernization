/* main(int): an implementation-defined form of main (C11 5.1.2.2.1p1); GCC and glibc pass it argc,
   which is 1 for a run without arguments (cirrun gives a main run without arguments argc = 1).
   Exit status 41 (run with MODE=status CASES=mainargs_cases.txt). */
int main(int level) {
  return 40 + level;
}

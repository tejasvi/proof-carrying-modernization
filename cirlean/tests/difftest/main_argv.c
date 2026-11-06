/* main(int, char **) run without arguments: argc = 1, argv[argc] a null pointer and argv[0] a
   modifiable string (C11 5.1.2.2.1p2; cirrun passes {"prog", NULL}, natively it is the program's
   name). Exit status 16 (run with MODE=status CASES=mainargs_cases.txt). */
int main(int argc, char **argv) {
  argv[0][0] = 'x';
  return argc * 10 + (argv[argc] == 0) * 5 + (argv[0][0] == 'x');
}

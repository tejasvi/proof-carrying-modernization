// Declared-only globals (run with CASES=externglob_cases.txt): a global the
// module only declares is defined in another translation unit or a library,
// so the module does not know its value: a read or a write is undefined
// ("external object without a model"), except the library's objects that are
// modelled: glibc's __libc_single_threaded, which is 1 in a single-threaded
// process, getopt's optind and opterr, 1 when a program starts, libm's
// signgam, where lgamma stores the sign of Gamma(x), and the C++ standard
// stream objects, live objects of indeterminate value that the stream models
// take (a read of one of their members is undefined). Expected result
// (labelled per case in the cases file): MATCH on the t_* cases; UB on the u_*
// cases (natively the library's object is read).
#include <errno.h>
#include <iostream>
#include <math.h>
#include <unistd.h>
#include <sys/single_threaded.h>

// glibc's single-threaded flag, modelled: 1
int t_single_threaded(int n) { return __libc_single_threaded + n; }

// std::cout and std::cerr as the stream of operator<< (an empty string: nothing
// is printed natively either)
int t_cout_print(int n) {
  std::cout << "";
  return n + 1;
}

int t_cerr_print(int n) {
  std::cerr << "" << "";
  return n + 2;
}

// getopt's opterr and optind, 1 at the start; a write to optind is the
// program's own
int t_opterr(int n) { return opterr + n; }

int t_optind(int n) { return optind + n; }

int t_optind_write(int n) {
  optind = n;
  return optind;
}

// signgam after lgamma: Gamma(-0.5) < 0, Gamma(2.5) > 0 (the arguments come from
// the parameter, so the compiler cannot fold the calls)
int t_signgam_neg(int n) {
  (void)lgamma(n - 3.5);
  return signgam + n;
}

int t_signgam_pos(int n) {
  (void)lgamma(n + 0.5);
  return signgam + n;
}

// environ and glibc's program_invocation_name: not modelled
int u_environ(int n) { return environ != nullptr ? n : 0; }

int u_progname(int n) { return program_invocation_name != nullptr ? n : 0; }

// std::cout's width, a field that the library's inline ios_base::width() reads
// through the stream object, whose value the module does not know
int u_iostream_field(int n) { return (int)std::cout.width() + n; }

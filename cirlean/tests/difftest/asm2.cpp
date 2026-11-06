// Inline asm with operands (run with CASES=asm2_cases.txt): with an empty
// template, an asm without outputs only reads its register inputs (a no-op; a
// memory input "m" is not read), an output tied to an input ("=r" with "0",
// "+r", and "+g", which CIR passes through memory) keeps that input's value,
// as the template leaves their shared register or memory unchanged, and an
// untied memory output ("=m", "+m") keeps its object's value. Expected result
// (labelled per case in the cases file): MATCH on the t_* cases; UB
// "unsupported operation cir.asm" on the u_* controls (an untied register
// output, a non-empty template, an output tied to a converted input), which
// stay outside the semantics.

struct P { int a, b; };

int t_in_reg(int n) {
  asm volatile("" : : "r"(n));
  return n + 1;
}

int t_in_escape(int n) {
  int x = n;
  asm volatile("" : : "r"(&x) : "memory");
  return x * 2;
}

int t_in_imr(int n) {
  asm("" : : "imr"(n), "imr"(n + 1));
  asm volatile("" : : "g"(n));
  asm volatile("" : : "i"(42), "n"(7));
  return n - 1;
}

int t_in_struct(int n) {
  P p = {n, n + 1};
  asm volatile("" : : "r"(&p), "r"(p.b) : "memory");
  return p.a * 10 + p.b;
}

int t_in_loop(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    s += i;
    asm volatile("" : : "r"(s) : "memory");
  }
  return s;
}

int t_tied(int n) {
  int y;
  asm("" : "=r"(y) : "0"(n));
  return y + 1;
}

int t_rw(int n) {
  asm("" : "+r"(n));
  return n * 3;
}

int t_rw_inputs(int n) {
  int a = n + 1, b = n + 2;
  asm volatile("" : "+r"(n) : "r"(a), "r"(b) : "memory");
  return n + a * 10 + b * 100;
}

int t_tied_ptr(int n) {
  int x = n;
  int *q;
  asm("" : "=r"(q) : "0"(&x));
  *q += 5;
  return x;
}

int t_rw_u16(int n) {
  unsigned short u = (unsigned short)n;
  asm("" : "+r"(u));
  return u;
}

int t_rw_double(int n) {
  double d = n * 0.5;
  asm("" : "+x"(d));
  return (int)(d * 4);
}

int t_rw_bool(int n) {
  bool b = n > 0;
  asm("" : "+r"(b));
  return b;
}

int t_tied_two(int n) {
  int x = n, y = 2 * n, a, b;
  asm("" : "=r"(a), "=r"(b) : "0"(x), "1"(y));
  return a * 10 - b;
}

int t_tied_second(int n) {
  int a;
  asm("" : "=r"(a) : "r"(n + 1), "0"(n));
  return a;
}

// a char tied to an int output: CIR sign-extends the char (`cir.cast`) before
// the asm, while Clang's and GCC's code zero-extend it into the register
int u_tied_char(int n) {
  char c = (char)n;
  int y;
  asm("" : "=r"(y) : "0"(c));
  return y;
}

#define OPT_BARRIER(x) __asm__ ("" : "=r" (x) : "0" (x))

int t_opt_barrier(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    int k = i;
    OPT_BARRIER(k);
    s += k;
  }
  return s;
}

int u_untied(int n) {
  int y;
  asm volatile("" : "=r"(y));
  return n;
}

int u_untied_in(int n) {
  int y;
  asm("" : "=r"(y) : "r"(n));
  return y;
}

int t_mem_in(int n) {
  asm volatile("" : : "m"(n));
  return n;
}

int t_mem_out(int n) {
  int x = n;
  asm volatile("" : "=m"(x));
  return x;
}

int t_rw_mem(int n) {
  asm volatile("" : "+m"(n));
  return n;
}

int t_rw_g(int n) {
  asm("" : "+g"(n));
  return n;
}

int u_tmpl(int n) {
  asm volatile("addl $1, %0" : "+r"(n));
  return n;
}

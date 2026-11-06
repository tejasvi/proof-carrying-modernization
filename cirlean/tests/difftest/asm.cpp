// Inline asm (run with CASES=asm_cases.txt): an asm statement with an empty
// template (or `nop`) and no operands, only clobbers
// (`asm volatile("" ::: "memory")`), is a compiler barrier, a no-op in the
// sequential semantics; with operands (inputs, outputs tied to inputs, memory
// operands) see asm2.cpp and gaps1.c. Expected result (labelled per case in
// the cases file): MATCH.

int t_asm_barrier(int n) {
  int s = 0;
  for (int i = 0; i < n; ++i) {
    s += i;
    asm volatile("" ::: "memory");
  }
  return s;
}

int t_asm_empty(int n) {
  asm("");
  return n + 1;
}

int t_asm_volatile(int n) {
  asm volatile("");
  asm volatile("");
  return n * 2;
}

static int bump(int *p) {
  *p += 3;
  asm volatile("" ::: "memory");
  return *p;
}

int t_asm_clobbers(int n) {
  int x = n;
  asm volatile("" ::: "cc", "memory");
  int y = bump(&x);
  asm volatile("" ::: "rax", "rdx");
  return x * 10 + y;
}

int t_asm_inout(int n) {
  asm("" : "+r"(n));
  return n + 1;
}

int t_asm_input(int n) {
  asm volatile("" : : "r"(n) : "memory");
  return n;
}

int t_asm_output(int n) {
  int r = n;
  asm volatile("" : "=r"(r) : "0"(n));
  return r;
}

int t_asm_nop(int n) {
  asm volatile("nop");
  return n;
}

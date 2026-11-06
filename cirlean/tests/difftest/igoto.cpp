// GNU computed goto (run with CASES=igoto_cases.txt): `&&label` is the label's
// address, `goto *p` jumps to it. Expected result (labelled per case in the cases
// file): MATCH on the t_ok_* cases; UB from cirrun on the t_ub_* cases (an
// indirect goto to a pointer that is not a label address or to a label of
// another function, a read through a label address: undefined; native runs
// crash or print whatever the machine code gives).

// a bytecode interpreter: a dispatch table of label addresses (function-local static array)
int t_ok_interp(int k) {
  static void *dispatch[] = {&&op_inc, &&op_dbl, &&op_dec, &&op_halt};
  const unsigned char code[] = {0, 1, 0, 1, 2, 1, 0, 3};
  int acc = k, pc = 0;
  goto *dispatch[code[pc++]];
op_inc:
  acc += 1;
  goto *dispatch[code[pc++]];
op_dbl:
  acc *= 2;
  goto *dispatch[code[pc++]];
op_dec:
  acc -= 3;
  goto *dispatch[code[pc++]];
op_halt:
  return acc * 10 + pc;
}

// label pointers in a static array, selected by the argument
int t_ok_static_table(int k) {
  static void *const table[] = {&&a, &&b, &&c};
  int r = 1;
  goto *table[(k % 3 + 3) % 3];
a:
  r += 100;
  goto done;
b:
  r += 200;
  goto done;
c:
  r += 300;
done:
  return r + k;
}

// computed goto inside nested loops (labels in the inner loop's body)
int t_ok_nested(int n) {
  int s = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < 4; j++) {
      void *p = ((i + j) % 3 == 0) ? &&zero : ((i + j) % 3 == 1) ? &&one : &&two;
      goto *p;
    zero:
      s += 1;
      goto next;
    one:
      s += 10;
      goto next;
    two:
      s += 100;
    next:;
    }
  }
  return s;
}

// computed goto out of nested loops to labels of the function body (a local
// array of label addresses)
int t_ok_escape(int k) {
  void *const exits[] = {&&found_even, &&found_odd};
  int s = 0;
  for (int i = 0; i < 10; i++)
    for (int j = 0; j < 10; j++) {
      s += i * j;
      if (s > k) goto *exits[(i + j) & 1];
    }
  return -1;
found_even:
  return s * 2;
found_odd:
  return s * 2 + 1;
}

// comparisons of label addresses
int t_ok_compare(int k) {
  void *a = &&l1, *b = &&l1, *c = &&l2;
  int r = (a == b) + 2 * (a == c) + 4 * (a != c) + 8 * (a != nullptr);
  if (k > 0) goto *c;
  goto *a;
l1:
  return r;
l2:
  return 100 + r;
}

// a label address stored in a struct and dispatched through it
struct Op { void *target; int arg; };
int t_ok_struct(int k) {
  Op ops[2] = {{&&add, 5}, {&&sub, 2}};
  int acc = 0;
  for (int i = 0; i < 2; i++) {
    goto *ops[(i + k) % 2].target;
  add:
    acc = acc * 3 + ops[0].arg;
    continue;
  sub:
    acc = acc * 3 - ops[1].arg;
  }
  return acc;
}

// UB: an indirect goto to a pointer that is not a label address (the function
// takes a label's address: clang rejects `goto *p` in a function that does not)
int t_ub_data_ptr(int k) {
  int x = k;
  void *p = k < -1000 ? &&out : (void *)&x;
  goto *p;
out:
  return x;
}

// UB: an indirect goto to the null pointer
int t_ub_null(int k) {
  void *p = k < -1000 ? &&out : nullptr;
  goto *p;
out:
  return k;
}

// UB: an indirect goto to a label of another function
static void *saved_label;
static int remember(int k) {
  saved_label = &&there;
  if (k < -1000) goto *saved_label;
  return k;
there:
  return -k;
}
int t_ub_other_fn(int k) {
  remember(k);
  void *p = k < -1000 ? &&here : saved_label;
  goto *p;
here:
  return k;
}

// UB: a read through a label address
int t_ub_read_label(int k) {
  const int *q = (const int *)&&l;
  if (k < -1000) goto *(void *)q;
  return *q + k;
l:
  return 0;
}

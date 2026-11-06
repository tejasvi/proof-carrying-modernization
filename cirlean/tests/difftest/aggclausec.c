/* The aggregate clause of C11 6.5p7 with C's struct assignment (a cir.copy;
   run with CASES=aggclause_cases.txt, which describes the cases). */

struct S { int a; int b; };
struct P { int x; int y; };

/* a structure of two ints assigned over an int member and the next one */
int ac_store_member(int k) {
  struct S s = {1, 2};
  struct P p = {5 + k, 6};
  *(struct P *)&s.a = p;
  return s.a * 10 + s.b;
}
/* the same over elements 1 and 2 of an int array */
int ac_store_elem(int k) {
  int arr[3] = {1, 2, 3};
  struct P p = {5 + k, 6};
  *(struct P *)&arr[1] = p;
  return arr[0] * 100 + arr[1] * 10 + arr[2];
}
/* a structure of two ints read over an int member and the next one */
int ac_load_member(int k) {
  struct S s = {1 + k, 2};
  struct P p = *(struct P *)&s.a;
  return p.x * 10 + p.y;
}
/* control: the second member falls outside the object */
int uc_store_past(int k) {
  struct S s = {1, 2};
  struct P p = {5 + k, 6};
  *(struct P *)&s.b = p;
  return s.b;
}

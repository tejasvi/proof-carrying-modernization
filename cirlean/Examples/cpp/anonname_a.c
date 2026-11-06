/* Linking units with free-standing anonymous structs (cir2lean --link, Examples/LinkAnon.lean):
   pa here and pb in anonname_b.c have the same layout but different member names, so they stay
   two types (C11 6.2.7p1); same_a and same_b have the same members and names, so they are one. */
struct { int x; int y; } pa;
struct { int p; int q; } same_a;

int ub(void);

int ua(void) {
  pa.x = 1;
  pa.y = 2;
  same_a.p = 3;
  same_a.q = 4;
  return pa.x + pa.y + same_a.p + same_a.q + ub();
}

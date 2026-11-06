/* The other unit of the anonymous-struct names case of Examples/LinkAnon.lean. */
struct { int u; int v; } pb;
struct { int p; int q; } same_b;

int ub(void) {
  pb.u = 5;
  pb.v = 6;
  same_b.p = 7;
  same_b.q = 8;
  return pb.u + pb.v + same_b.p + same_b.q;
}

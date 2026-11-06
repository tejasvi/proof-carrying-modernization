/* C side of the C -> Rust struct demo; the Rust side is examples/rust/point/src/lib.rs. */
struct Point {
  int x;
  int y;
};

/* |x| + |y| of a point passed by pointer */
int manhattan(const struct Point *p) {
  int ax = p->x < 0 ? -p->x : p->x;
  int ay = p->y < 0 ? -p->y : p->y;
  return ax + ay;
}

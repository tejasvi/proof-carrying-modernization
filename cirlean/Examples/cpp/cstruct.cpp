// Loop state kept in a struct of the caller (the C parser/iterator idiom).
struct counter {
  int pos;
  int total;
};

void advance(struct counter *c, int n) {
  for (; c->pos < n; c->pos++)
    c->total += 2;
}

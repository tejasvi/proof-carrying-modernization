// An array of structs written through a pointer to one element: the C token
// array idiom of parsers such as jsmn (`fill_token(&tokens[i], ...)`).
struct tok {
  unsigned type;
  int start;
  int end;
  int size;
};

void fill_token(struct tok *t, unsigned type, int start, int end) {
  t->type = type;
  t->start = start;
  t->end = end;
  t->size = 0;
}

int add_token(struct tok *toks, int n, int *next, int start, int end) {
  if (*next >= n)
    return -1;
  struct tok *t = &toks[(*next)++];
  fill_token(t, 1, start, end);
  return 0;
}

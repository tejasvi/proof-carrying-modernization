/* Loops that write through pointer parameters: an array written through a
   pointer, a pointer of the caller moved through a pointer to it (as cJSON's
   skip_oneline_comment), and a copy with a write index (Examples/PtrArgs.lean). */
/* an array written through a pointer parameter */
void fill_buf(char *buf, int n, char c) {
  for (int i = 0; i < n; i++) buf[i] = c;
}
/* a pointer of the caller moved through a pointer to it (cJSON's skip_oneline_comment) */
void skip_spaces(const char **input) {
  while (**input == ' ') (*input)++;
}
/* reads s, writes the non-space characters into out */
int copy_nonspace(const char *s, char *out, int n) {
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (s[i] != ' ') { out[k] = s[i]; k++; }
  }
  return k;
}

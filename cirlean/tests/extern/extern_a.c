/* Unit a of the declared-only global test (tests/ExternGlob.lean): reads a
   global that unit b defines. */
extern int shared_count;
int read_shared(void) { return shared_count + 1; }

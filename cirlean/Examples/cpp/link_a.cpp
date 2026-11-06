// Translation unit a of the linking example (Examples/Link.lean).
extern "C" {
static int helper(int x) { return x + 1; }
static const char *tag = "unit-a";
int twice(int x);
int run(void) { return twice(helper(3)) + (tag[0] == 'u' ? 0 : 100); }
}

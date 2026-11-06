// Translation unit b of the linking example (Examples/Link.lean).
extern "C" {
static int helper(int x) { return x * 10; }
static const char *tag = "b";
int twice(int x) { return helper(x) / 5 + (tag[0] == 'b' ? 0 : 1000); }
}

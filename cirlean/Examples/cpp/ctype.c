/* Character classes with glibc headers: isdigit/isalpha are macros over
   the table returned by __ctype_b_loc() (Examples/Ctype.lean). */
#include <ctype.h>
int match_digit(char c) { return isdigit(c); }
int match_alpha(char c) { return isalpha(c); }

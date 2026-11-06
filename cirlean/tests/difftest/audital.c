/* Aliases after rog's second audit of next3 (CASES=audital_cases.txt): the q_* functions are rog's
   (soundaudit_n3: n3p7.c, n3p8.c), the t_* ones this branch's. A global alias names its target's
   object; a function alias declared with another type than its target is no other name of it. */

/* a function alias with another prototype than its target (6.5.2.2p9) */
int ag(int x) { return x + 1; }
long af(long) __attribute__((alias("ag")));
int q_alias_other_type(int k) { return (int)af(5L + k); }
/* a variable alias */
int gv = 5;
extern int av __attribute__((alias("gv")));
int q_variable_alias(int k) { av = av + k; return gv * 10 + av; }

int gw = 5;
extern int aw __attribute__((alias("gw")));
/* a write through the alias, then the target read: 7 */
int q_variable_alias_write(int k) { aw = 7 + k; return gw; }
/* a write to the target, then the alias read */
int q_variable_alias_read(int k) { gw = 8 + k; return aw; }

/* --- this branch's */
/* the alias and its target are one object: one address (6.5.9p6) */
int t_variable_alias_address(int k) { return (&av == &gv) * 10 + k; }
/* an alias of an alias, and an array alias written through its element */
int ga[3] = {1, 2, 3};
extern int ab[3] __attribute__((alias("ga")));
extern int ac[3] __attribute__((alias("ab")));
int t_array_alias_of_alias(int k) {
  ac[1] = 20 + k;
  return ga[1] * 100 + ab[0] * 10 + ac[2];
}
/* a function alias with the target's prototype: a call runs the target */
int ah(int) __attribute__((alias("ag")));
int t_alias_same_type(int k) { return ah(k) * 10 + ag(k); }

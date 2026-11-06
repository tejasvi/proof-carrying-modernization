// Pointer arguments, after (cidemo 018ebeb): for -> while, swap's writes in the other order (the
// arguments may alias), a conditional expression.
int sum_arr(const int *a, int n) {
    int s = 0;
    int i = 0;
    while (i < n) {                             /* refactor: for -> while */
        s = s + a[i];
        i = i + 1;
    }
    return s;
}

void swap(int *a, int *b) {
    int t = *b;                                 /* refactor: other order (a and b may alias) */
    *b = *a;
    *a = t;
}

int get_or(const int *p, int d) {
    return p ? *p : d;                          /* refactor: conditional expression */
}

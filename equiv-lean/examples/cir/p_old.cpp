// Pointer arguments, before (veriforch's cidemo at b88e74c): an array sum, swap, a guarded read.
int sum_arr(const int *a, int n) {
    int s = 0;
    for (int i = 0; i < n; i++) {
        s = s + a[i];
    }
    return s;
}

void swap(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
}

int get_or(const int *p, int d) {
    if (p == 0) return d;
    return *p;
}

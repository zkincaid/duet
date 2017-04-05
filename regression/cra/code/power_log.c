int pow2(int n) {
    int i;
    int r = 1;
    __VERIFIER_assume(n > 0);
    for(i = 0; i < n; i++) {
	r *= 2;
    }
    return r;
}

int log2(int n) {
    int i;
    int r = 0;
    // We can't handle this if we replace the conditional with i != n.
    __VERIFIER_assume(n > 0);
    for(i = 1; i != n; i *= 2) {
	r ++;
    }
    return r;
}

void main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assert(n == log2(pow2(n)));
}

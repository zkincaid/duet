void main() { 
    int i, n = __VERIFIER_nondet_int(), q = __VERIFIER_nondet_int(), r;
    r = n;
    __VERIFIER_assume(n > q);
    __VERIFIER_assume(q >= 1);
    i = 0;
    while(r > q) {
	r = r - q;
	i = i + 1;
    }
    __VERIFIER_assert(i * q + r == n);
}

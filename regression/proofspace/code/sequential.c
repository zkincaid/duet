void main() {
    int x;
    int i;
    x = __VERIFIER_nondet_int();
    __VERIFIER_assume(x >= 0);
    i = 0;
    while (i < x) {
	i++;
    }
    __VERIFIER_assert(i == x);
}

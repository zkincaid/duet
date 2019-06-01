void main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 0);
    int x=n, c=0, r=0;

    while (x>0) {
	x--;
	if (__VERIFIER_nondet_int())
		r++;
	else
		while(r>0) {
			r--; c++;
		}
}
    __VERIFIER_assert(c <= n);
}

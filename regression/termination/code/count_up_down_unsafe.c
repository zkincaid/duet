void main() {
    int n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 0);
    int x=n, y=0;
    while(x>0) {
	x--;
	y++;
    }
    __VERIFIER_assert(y != n);
}

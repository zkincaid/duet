void main () {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int q = 0;
    int r = x;
    __VERIFIER_assume(y >= 0);
    while (r > y) {
        //r = r - y;
    	int tmp;
    	tmp = y;
    	while (tmp > 0) {
	    tmp = tmp - 1;
            r = r - 1;
        }
	q = q + 1;
    }
    __VERIFIER_assert(x == q*y + r);
}

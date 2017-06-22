/* Source: Tachio Terauchi and Alex Aiken: Secure Information Flow as a Safety
   Problem, SAS 2005.  Figure 5. */
void main() {
    int f11, f12, n1, k1, l1;
    int f21, f22, n2, k2, l2;
    __VERIFIER_assume(f11 == f21);
    __VERIFIER_assume(f12 == f22);
    __VERIFIER_assume(n1 == n2);
    __VERIFIER_assume(k1 == k2);
    __VERIFIER_assume(l1 == l2);
    // variant 1
    while(n1 > 0) {
	f11 = f11 + f12;
	f12 = f11 - f12;
	n1 --;
    }
    if (f11 > k1) {
	l1 = 1;
    } else {
	l1 = 0;
    }
    // variant 2
    while(n2 > 0) {
	f21 = f21 + f22;
	f22 = f21 - f22;
	n2 --;
    }
    if (f21 > k2) {
	l2 = 1;
    } else {
	l2 = 0;
    }
    __VERIFIER_assert(l1 == l2);
}

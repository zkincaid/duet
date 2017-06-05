int n;
int m;
void mult(int r, int i) {
    if (i < n) {
	mult(r + m, i + 1);
    } else {
	__VERIFIER_assert(r == m * n);
    }
}
void main() { 
    __VERIFIER_assume(n > 0);
    mult(0, 0);
}

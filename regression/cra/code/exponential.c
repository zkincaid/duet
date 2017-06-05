void main() {
    int i;
    int j, k;
    int n;
    j = k = 1;
    __VERIFIER_assume(n >= 1);    
    for(i = 0; i < n; i++) {
	j = 2*j;
    }
    for(i = 0; i < n; i++) {
	k = 2*k;
    }
    __VERIFIER_assert(j == k);
}

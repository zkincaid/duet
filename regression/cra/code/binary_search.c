int __cost;

void search(int n) {
    int lo = 1;
    int hi = n;
    while (lo <= hi) {
	int mid = lo + (hi-lo)/2;
	__cost++;
	if (__VERIFIER_nondet()) {
	    return;
	} else if (__VERIFIER_nondet()) {
	    lo = mid + 1;
	} else {
	    hi = mid - 1;
	}
    }
}
void main() {
    int n = __VERIFIER_nondet_int();
    __cost = 0;
    search(n);
}

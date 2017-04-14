int __cost;
void logn(int n) {
    int i;
    __VERIFIER_assume(n > 0);
    for(i = 1; i < n; i *= 2) {
	__cost ++;
    }
}

void nlogn(int n) {
    int i;
    __VERIFIER_assume(n > 0);
    for(i = 0; i < n; i ++) {
	__cost ++;
	logn(n);
    }
}

int main() {
    int n = __VERIFIER_nondet_int();
    nlogn(n);
}

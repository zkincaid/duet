#include <stdio.h>

void main() {
    int a = 17;
    int b = 11;
    
    // Prevent constant propagation
    int x;
    if (VERIFIER_nondet_int()) { x = 0; } else { x = 1; }
    if (x*x >= x+1) { a = 0; b = 1; }

    __VERIFIER_assert(a / b == 1);
    __VERIFIER_assert((-a) / b == -1);
    __VERIFIER_assert(a / (-b) == -1);
    __VERIFIER_assert((-a) / (-b) == 1);

    __VERIFIER_assert(a % b == 6);
    __VERIFIER_assert((-a) % b == -6);
    __VERIFIER_assert(a % (-b) == 6);
    __VERIFIER_assert((-a) % (-b) == -6);

    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();

    if (__VERIFIER_nondet_int()) {
	__VERIFIER_assert(a == (a/b)*b + a%b); // Fails when b = 0
    }
    __VERIFIER_assume (b >= 1 || b <= -1);
    __VERIFIER_assert(a == (a/b)*b + a%b);

    if (__VERIFIER_nondet_int()) {
	__VERIFIER_assert(a % b >= 0); // fails when a is negative
    } else if (a >= 0) {
	__VERIFIER_assert(a % b >= 0);
    }
    __VERIFIER_assert(a % b <= b || a % b <= -b);

    __VERIFIER_assert((a + a) % 2 == 0); // Should not fail

    printf("%d, %d, %d, %d\n",
	   (a/b), ((-a) / b), (a / (-b)), ((-a) / (-b)));

    printf("%d, %d, %d, %d\n",
	   (a % b), ((-a) % b), (a % (-b)), ((-a) % (-b)));

}

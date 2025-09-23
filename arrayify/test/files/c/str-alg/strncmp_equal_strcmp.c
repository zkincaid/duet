extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
    int size_a = __VERIFIER_nondet_int();
    int size_b = __VERIFIER_nondet_int();
    char a[size_a];
    init(size_a, a);
    char b[size_b];
    init(size_b, b);
    int n = __VERIFIER_nondet_int();
    int v1 = strcmp(a, b);
    int v2 = strncmp(a, b, n);
    if(v2 != 0) {
        __JVERIFIER_assert(v1 == v2);
    }
    return 0;
}

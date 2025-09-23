extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"
//memcmp(a, b, strlen(a) + 1) = strcmp(a, b)

int main() {
    int size_a = __VERIFIER_nondet_int();
    int size_b = __VERIFIER_nondet_int();
    char a[size_a];
    init(size_a, a);
    char b[size_b];
    init(size_b, b);
    int n = strlen(a);
    int v1 = strcmp(a, b);
    int v2 = memcmp2(a, b, n + 1);
    __JVERIFIER_assert(v1 == v2);
    return 0;
}

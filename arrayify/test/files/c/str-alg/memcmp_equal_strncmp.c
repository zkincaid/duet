extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"
//strncmp(a, b, n) = memcmp(a, b, n)

int main() {
    int size_a = __VERIFIER_nondet_int();
    int size_b = __VERIFIER_nondet_int();
    char a[size_a];
    init(size_a, a);
    char b[size_b];
    init(size_b, b);
    size_t n = strlen(a);
    int v1 = strncmp(a, b, n);
    int v2 = memcmp2(a, b, n);
    __JVERIFIER_assert(v1 == v2);
    return 0;
}

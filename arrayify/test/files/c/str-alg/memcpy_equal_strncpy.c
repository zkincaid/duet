extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
    int size = __VERIFIER_nondet_int();
    char a[size];
    init(size, a);
    char dst1[size];
    char dst2[size];
    size_t n = __VERIFIER_nondet_int();
    memcpy2(dst1, a, n);
    strncpy(dst2, a, n);
    if(n <= strlen(a)) {
        for(int i = 0; i < n; i++) {
            __JVERIFIER_assert(dst1[i] == dst2[i]);
        }
    }
    return 0;
}

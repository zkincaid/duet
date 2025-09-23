extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
    int size_a = __VERIFIER_nondet_int();
    char a[size_a];
    init(size_a, a);
    int n = strlen(a);
    char* p = strchr(a, '\0');
    __JVERIFIER_assert(n == p - a);
    return 0;
}

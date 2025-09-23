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
    char lookup = __VERIFIER_nondet_char();
    char* f = strchr(a, lookup);
    char* l = strchr(a, lookup);
    __JVERIFIER_assert(f == '\0' && l == '\0' || f != '\0' && l != '\0');
    return 0;
}

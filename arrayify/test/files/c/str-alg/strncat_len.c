extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"


int main() {
    int size = __VERIFIER_nondet_int();
    char hd1[size];
    char hd2[size];
    char tl[size]; 
    init(size, hd1);
    init(size, tl);
    strcpy(hd2, hd1);
    size_t n1 = __VERIFIER_nondet_int();
    size_t n2 = __VERIFIER_nondet_int();

    strncat(hd1, tl, n1);
    strncat(hd2, tl, n2);
    if(n1 <= n2) {
        __JVERIFIER_assert(strlen(hd1) <= strlen(hd2));
    }

    return 0;
}

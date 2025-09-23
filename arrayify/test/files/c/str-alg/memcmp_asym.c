extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"
//memcmp(a, b, n) <= 0 /\ memcmp(b, a, b) <= 0 => memcmp(a, b, n) = 0

int main() {
    int size = __VERIFIER_nondet_int();
    char a[size]; 
    init(size, a);
    int size_b = __VERIFIER_nondet_int();
    char b[size_b];
    init(size_b, b);

    size_t n =  __VERIFIER_nondet_int();
    int a_b = memcmp2(a, b, n);
    int b_a = memcmp2(b, a, n);
    if (a_b <= 0 && b_a <= 0){
        __JVERIFIER_assert(a_b == 0);
    }
    return 0;
}

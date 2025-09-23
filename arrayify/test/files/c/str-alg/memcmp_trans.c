extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"


int main() {
    int size_a = __VERIFIER_nondet_int();
    int size_b = __VERIFIER_nondet_int();
    int size_c = __VERIFIER_nondet_int();
    char a[size_a];
    init(size_a,a);
    char b[size_b];
    init(size_b, b);
    char c[size_c];
    init(size_c, c);


    size_t n =  __VERIFIER_nondet_int();
    int a_b = memcmp2(a, b, n);
    int a_c = memcmp2(a, c, n);
    int b_c = memcmp2(b, c, n);
    //TODO: This assertion is wrong... correct it
    if (a_b == b_c){
        __JVERIFIER_assert(a_b == a_c);
    }
    return 0;
}

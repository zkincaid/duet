extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"


int main() {
    int size = __VERIFIER_nondet_int();
    int ch = __VERIFIER_nondet_int();
    char a1[size];
    char b1[size]; 
    init(size, a1);
    init(size, b1);
    char* index = strchr(a1, ch); 
    strcat(a1, b2);
    if(index != '\0') {
        __JVERIFIER_assert(strchr(a1, ch) == index);
    }
    return 0;
}

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"


int main() {
    int size = __VERIFIER_nondet_int();
    int ch = __VERIFIER_nondet_int();
    char a[size];
    char b[size]; 
    init(size, a);
    init(size, b);
    char* index = strrchr(a, ch); 
    strcat(a, b);
    if(index != NULL) {
        __JVERIFIER_assert(strchr(a, ch) - a - strlen(a)  == index - b);
    }
    return 0;
}

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
    if(strchr(a1, ch) == '\0' && strchr(b1, ch) == '\0') {
        strcat(a1, b1);
        __JVERIFIER_assert(strchr(a1, ch) == '\0');
    }
    return 0;
}

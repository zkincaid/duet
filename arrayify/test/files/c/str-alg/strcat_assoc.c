extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
    __VERIFIER_error(); 
} }
extern int __VERIFIER_nondet_int();
#include "string.h"


int main() {
    int size = __VERIFIER_nondet_int();
    char a1[size];
    char b1[size]; 
    char c1[size]; 
    init(size, a1);
    init(size, b1);
    init(size, c1);
    char a2[size];
    char b2[size]; 
    char c2[size]; 
    strcpy(a2, a1);
    strcpy(b2, b1);
    strcpy(c2, c1);
    strcat(c2, b2);
    strcat(c2, a2);
    strcat(b1, a1);
    strcat(c1, b1);
    __JVERIFIER_assert(strcmp(c1, c2) == 0);
    return 0;
}

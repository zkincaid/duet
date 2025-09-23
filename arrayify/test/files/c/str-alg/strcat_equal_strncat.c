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
    init(size, a1);
    init(size, b1);
    char a2[size];
    char b2[size]; 
    strcpy(a2, a1);
    strcpy(b2, b1);
    strcat(a1, b1);
    strncat(a2, b2, strlen(b2));
    __JVERIFIER_assert(strcmp(a1, a2) == 0);
    return 0;
}

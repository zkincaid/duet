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
    strncat(hd1, tl, 0); 
    __JVERIFIER_assert(strlen(hd1) == strlen(hd2));

    return 0;
}

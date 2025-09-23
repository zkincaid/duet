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
    char b[size]; 
    char c[size]; 
    init(size, hd1);
    init(size, b);
    init(size, c);
    strcpy(hd2, hd1);
    size_t n = strlen(hd1);
    strcat(hd1, b);
    strcat(hd2, c);
    __JVERIFIER_assert(strncmp(hd1, hd2, n) == 0);
    return 0;
}

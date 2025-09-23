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
    char o[2*size];
    init(size, hd1);
    init(size, b);
    init(2*size, o);
    strcpy(hd2, hd1);
    strcat(hd1, b);
    if(strcmp(o, hd1) == 0) {
        size_t n = __VERIFIER_nondet_int();
        strncat(hd2, b, n);
        __JVERIFIER_assert(strncmp(o, hd2, strlen(hd2)) == 0);
    }
    return 0;
}

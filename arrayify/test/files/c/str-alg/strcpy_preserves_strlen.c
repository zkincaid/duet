extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char src[size];
  init(size, src);
  char dest[size];
  strcpy(dest, src);
  __JVERIFIER_assert(strlen(src) == strlen(dest)) ;
  return 0;
}

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char src[size];
  init(size, src);
  char dest1[size];
  strcpy(dest1, src);
  char dest2[size];
  strcpy(dest2, src);
  __JVERIFIER_assert(strcmp(dest1, dest2) == 0);
  return 0;
}

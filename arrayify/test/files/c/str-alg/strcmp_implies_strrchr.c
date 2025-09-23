extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char a[size];
  char b[size];
  init(size, a);
  init(size, b);
  char lookup = __VERIFIER_nondet_char();
  char* pa = strrchr(a, lookup);
  char* pb = strrchr(b, lookup);
  if(strcmp(a, b) == 0) { 
      __JVERIFIER_assert(pa == '\0' && pb == '\0' || pa- a == pb - b) ;
  }
  return 0;
}

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  int ch = __VERIFIER_nondet_int();
  size_t n = __VERIFIER_nondet_int();
  int ch2 = __VERIFIER_nondet_int();
  size_t n2 = __VERIFIER_nondet_int();

  char str[size];
  memset2(str, ch, n);
  memset2(str, ch2, n2);
  for(size_t i = n2; i < n1; i ++)
  {
      __JVERIFIER_assert(str[i] == ch) ;
      i++;
  }
  return 0;
}

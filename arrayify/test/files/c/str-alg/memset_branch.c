extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  int ch = __VERIFIER_nondet_int();
  size_t n = __VERIFIER_nondet_int();
  char str1[size];
  char str2[size];
  memset2(str1, ch, n);
  memset2(str2, ch, n);
  for(size_t i = 0; i < n; i ++)
  {
     __JVERIFIER_assert(str1[i] == str2[i]) ;
     i++;
  }
  return 0;
}

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  size_t n = __VERIFIER_nondet_int();
  char src[size];
  init(size, src);
  char dest1[size];
  memcpy2(dest1, src, n);
  char dest2[size];
  memcpy2(dest2, src, n);
  for(size_t i = 0; i < n; i ++)
  {
     __JVERIFIER_assert(dest2[i] == dest1[i]) ;
     i++;
  }
  return 0;
}

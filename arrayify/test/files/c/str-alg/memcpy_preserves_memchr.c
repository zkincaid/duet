extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  size_t n1 = __VERIFIER_nondet_int();
  size_t n2 = __VERIFIER_nondet_int();
  char src[size];
  char dst[size];
  init(size, src);
  memcpy2(dst,src, n1);
  if(n1 >= n2) {
      char lookup = __VERIFIER_nondet_char();
      char* index = memchr2(src, lookup, n2);
      char* index2 = memchr2(dst, lookup, n2);
      __JVERIFIER_assert(index == index2);
  }
  return 0;
}

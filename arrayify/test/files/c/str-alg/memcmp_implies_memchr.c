extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"
//memcmp(a, b, n) = 0 => memchr(a, c, n) = memchr (b, c, n)

int main() {
  int size = __VERIFIER_nondet_int();
  size_t n1 = __VERIFIER_nondet_int();
  size_t n2 = __VERIFIER_nondet_int();
  char str1[size];
  char str2[size];
  init(size, str1);
  init(size, str2);
  if(memcmp2(str1, str2, n1) == 0) {
      char lookup = __VERIFIER_nondet_char();
      char* index = memchr2(str1, lookup, n1);
      char* index2 = memchr2(str2, lookup, n1);
      __JVERIFIER_assert(index == index2);
  }
    return 0;
}

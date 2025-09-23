extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"
//memcmp(a, b, n) = 0 /\ n >= o => memcmp(a, b, o) = 0

int main() {
  int size = __VERIFIER_nondet_int();
  size_t n1 = __VERIFIER_nondet_int();
  size_t n2 = __VERIFIER_nondet_int();
  char str1[size];
  char str2[size];
  init(size, str1);
  init(size, str2);
  if(n1 >= n2 && memcmp2(str1, str2, n1) == 0) {
      __JVERIFIER_assert(memcmp2(str1, str2, n2) == 0);
  }
    return 0;
}

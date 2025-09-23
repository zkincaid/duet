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
  char str[size];
  char dst[size];
  init(size, str);
  char lookup = __VERIFIER_nondet_char();
  char set = __VERIFIER_nondet_char();
  memset2(str, set, n1);
  if(set != lookup && n1 >= n2) {
      char* index = memchr2(str, lookup, n2);
      __JVERIFIER_assert(index == '\0');
  }
  return 0;
}

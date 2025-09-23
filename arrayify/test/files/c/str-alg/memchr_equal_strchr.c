extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"
//strchr(str, c) = memchr(str, c, strlen(str))

int main() {
  int size = __VERIFIER_nondet_int();
  char str[size];
  init(size, str);
  char lookup = __VERIFIER_nondet_char();
  int len = strlen(str);
  char* index = memchr2(str, lookup, len);
  char* index2 = strchr(str, lookup);
  __JVERIFIER_assert(index == index2);
  return 0;
}

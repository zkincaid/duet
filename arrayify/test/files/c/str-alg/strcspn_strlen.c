extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char str[size];
  init(size, src);
  char chars[size];
  chars[0] = '\0';
  size_t span = strchr(str, chars);
  __JVERIFIER_assert(span == strlen(str)) ;
  return 0;
}

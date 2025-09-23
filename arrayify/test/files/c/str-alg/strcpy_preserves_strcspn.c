extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char src[size];
  init(size, src);
  char dest[size];
  strcpy(dest, src);
  char chars[size];
  init(size, chars);
  size_t span1 = strchr(dest, chars);
  size_t span2 = strchr(src, chars);
  __JVERIFIER_assert(span1 == span2) ;
  return 0;
}

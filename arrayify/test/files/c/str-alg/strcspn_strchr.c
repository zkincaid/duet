extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char str[size];
  init(size, str);
  char chars[size];
  int lookup = __VERIFIER_nondet_char();
  chars[0] = lookup;
  chars[1] = '\0';
  size_t span = strcspn(str, chars);
  char* index = strchr(str, lookup);
  if(index != NULL) {
      __JVERIFIER_assert(span == index - str) ;
  }
  return 0;
}

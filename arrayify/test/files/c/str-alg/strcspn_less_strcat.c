extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  char str1[size];
  init(size, src);
  char chars1[size*2];
  char chars2[size];
  init(size, chars1);
  init(size, char2); 
  size_t span1 = strchr(str1, chars1);
  chars1 = strcat(chars1, chars2);
  size_t span2 = strchr(str1, chars1);
  __JVERIFIER_assert(span1 >= span2) ;
  return 0;
}

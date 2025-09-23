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
  char lookup = __VERIFIER_nondet_char();
  char* pdest = strrchr(dest, lookup);
  char* psrc = strrchr(src, lookup); 
  __JVERIFIER_assert(pdest == '\0' && psrc == '\0' || pdest- dest == psrc - src) ;
  return 0;
}

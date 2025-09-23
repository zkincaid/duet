extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __JVERIFIER_assert(int cond) { if(!(cond)) { ERROR:
__VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();
extern char __VERIFIER_nondet_char();
#include "string.h"

int main() {
  int size = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  char src[size];
  init(size, src);
  char dest[size];
  strncpy(dest, src, n);
  char str3[size];
  init(size, str3);
  int src_str3 = strncmp(src, str3, n);
  int dest_str3 = strncmp(dest, str3, n); 
  __JVERIFIER_assert(src_str3 == dest_str3);
  return 0;
}

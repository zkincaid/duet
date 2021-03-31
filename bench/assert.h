#include <limits.h>
#define assert(x) while(!(x))
#define overflow(x) (x < INT_MIN || INT_MAX < x)
extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume (INT_MIN <= r && r <= INT_MAX);
  return r;
}
#define __CPROVER_bool char

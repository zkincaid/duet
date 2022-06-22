#include "assert.h"

#include "tick.h"

int main()
{
	init_tick(0);

	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(n > 0);
	int p = __VERIFIER_nondet_int();
	__VERIFIER_assume(p > 0);
    int x = 0, y = 0;
    while (x + y < n) {
      int t = __VERIFIER_nondet_int();
      __VERIFIER_assume(t > 0);
      x = x + t * t;
      y = y - t * t + p;
      tick(1);
      }

	int mainbnd = n;
	__VERIFIER_assert(p * __cost >= mainbnd);
	return 0;
}

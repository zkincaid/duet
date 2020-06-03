#include "assert.h"

// C4B output: 1+2|[0,n]|

#include "tick.h"

void start(int n, int m)
{
	int va = n;
	int vb = 0;
	__VERIFIER_assume(n > 0 && m > 0);

	while (va > 0 && __VERIFIER_nondet_int()) {
		tick(1);
		if (vb < m) { 
			vb = vb + 1; 
			va = va - 1;
		} else {
			vb = 0;
		}
	}
}

int main() 
{
	init_tick(0);
	int n = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();
	
	start(n, m);
	
	int bnd = 1 + 2 * (n > 0 ? n : 0);
	__VERIFIER_assert(__cost <= bnd);
	return 0;
}

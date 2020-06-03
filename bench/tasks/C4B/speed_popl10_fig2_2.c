#include "assert.h"

// C4B output: |[x,n]|+|[z,n]|

#include "tick.h"

void start(int x, int z, int n)
{
	while (x < n) {
		tick(1);
		if (z > x)
			x = x + 1;
		else
			z = z + 1;
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	
	start(x, z, n);
	
	int bnd = ((n > x) ? (n - x) : 0) + ((n > z) ? (n - z) : 0);
	__VERIFIER_assert(__cost <= bnd);
	return 0;
}

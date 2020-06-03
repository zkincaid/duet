#include "assert.h"

// C4B output: 101|[0,x]|

#include "tick.h"

void start(int x, int y)
{
	int z;

	__VERIFIER_assume(y >= 0);

	while (x > y) {
	        tick(1);
		x -= y + 1;
		z = 100 + 2 * y;
		while (z > 0) {
			tick(1);
			z--;
		}
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = 101 * ((x > 0) ? x : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

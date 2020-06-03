#include "assert.h"

// C4B output: 1.33|[y,z]|+0.33|[0,y]|

#include "tick.h"

void start(int y, int z)
{
	while (z > y) {
		tick(1);
		y = y + 1;
	}
	while (y > 2) {
		tick(1);
		y = y - 3;
	}
}

int main() 
{
	init_tick(0);

	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();

	start(y, z);
	
	int bnd = 4 * ((z > y) ? (z - y) : 0) + ((y > 0) ? y : 0);
	__VERIFIER_assert(3 * __cost <= bnd);
	
	return 0;
}

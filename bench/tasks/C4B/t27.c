#include "assert.h"

// C4B output: 0.01|[n,y]|+11|[n,0]|

#include "tick.h"

void start(int n, int y)
{
	while (n < 0) {
		n++;
		y += 1000;
		while (y >= 100) {
			tick(1);
			y -= 100;
		}
	}
}

int main() 
{
	init_tick(0);

	int n = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(n, y);
	
	int bnd = ((y > n) ? (y - n) : 0) + 1100 * ((n < 0) ? -n : 0);
	__VERIFIER_assert(100*__cost <= bnd);
	
	return 0;
}

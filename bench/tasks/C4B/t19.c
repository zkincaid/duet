#include "assert.h"

// C4B output: 50+|[-1,i]|+|[0,k]|

#include "tick.h"

void start(int i, int k)
{
	while (i > 100) {
		tick(1);
		i--;
	}
	i = i + k + 50;
	while (i >= 0) {
		tick(1);
		i--;
	}
}

int main() 
{
	init_tick(0);

	int i = __VERIFIER_nondet_int();
	int k = __VERIFIER_nondet_int();

	start(i, k);
	
	int bnd = 50 + ((i > -1) ? (i + 1) : 0) + ((k > 0) ? k : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

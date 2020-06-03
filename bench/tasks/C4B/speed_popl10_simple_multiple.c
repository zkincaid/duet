#include "assert.h"

// C4B output : |[0,m]|+|[0,n]|

#include "tick.h"

void start(int n, int m)
{
	int x = 0;
	int y = 0;

	while (x < n) {
		tick(1);
		if (y < m)
			y = y + 1;
		else
			x = x + 1;
	}
}

int main() 
{
	init_tick(0);
	
	int n = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();

	start(n, m);
	
	int bnd = ((n > 0) ? n : 0) + ((m > 0) ? m : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

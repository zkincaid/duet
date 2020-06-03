#include "assert.h"

// C4B output: |[x,n]|+|[y,m]|

#include "tick.h"

void start(int x, int y, int n, int m)
{
	while (n > x) {
		tick(1);
		if (m > y) 
			y = y + 1;
		else
			x = x + 1;
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();
	
	start(x, y, n, m);
	
	int bnd = ((n > x) ? (n - x) : 0) + ((m > y) ? (m - y) : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

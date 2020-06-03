#include "assert.h"

//C4B output: 2.00 |[0, n]|

#include "tick.h"

void start(int n)
{
	int x = 0;
	int y = 0;

	for (;;) {
		if (x < n) {
			y = y + 1;
			x = x + 1;
		} 
		else if (y > 0) {
			y = y - 1;
		}
		else
			break;
		tick(1);
	}
}

int main() 
{
	init_tick(0);
	
	int n = __VERIFIER_nondet_int();
	
	start(n);
	
	int bnd = 2 * (n>0?n:0);
	__VERIFIER_assert (__cost <= bnd);
	return 0;
}


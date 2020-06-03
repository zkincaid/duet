#include "assert.h"

// C4B output: |[y,x]|

#include "tick.h"

void start(int x, int y)
{
	while (x > y) {
		tick(1);
		if (__VERIFIER_nondet_int())
			y = y + 1;
		else
			x = x - 1;
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = (x > y) ? (x - y) : 0;
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

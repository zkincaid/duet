#include "assert.h"

// C4B output: |[0,x]|+|[0,y]|

#include "tick.h"

void start(int x, int y)
{
	int t;

	while (x > 0) {
		tick(1);
		x--;
		t=x, x=y, y=t;
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = ((x > 0) ? x : 0) + ((y > 0) ? y : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

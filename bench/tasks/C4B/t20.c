#include "assert.h"

// C4B output: |[x,y]|+|[y,x]|

#include "tick.h"

void start(int x, int y)
{
	while (x < y) {
		x++;
		tick(1);
	}
	while (y < x) {
		y++;
		tick(1);
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = (x > y) ? (x - y) : (y - x);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

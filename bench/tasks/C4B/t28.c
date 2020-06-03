#include "assert.h"

// C4B output: |[x,0]|+|[0,y]|+1002|[y,x]|

#include "tick.h"

void start(int x, int y)
{
	while (x > y) {
		tick(1);
		x--;
		x += 1000;
		y += 1000;
	}

	while (y > 0) {
		tick(1);
		y--;
	}
	while (x < 0) {
		tick(1);
		x++;
	}
}

int main() 
{
	init_tick(0);

	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();

	start(x, y);
	
	int bnd = ((x < 0) ? -x : 0) + ((y > 0) ? y : 0) + 1002 * ((x > y) ? (x - y) : 0);
	__VERIFIER_assert(__cost <= bnd);
	
	return 0;
}

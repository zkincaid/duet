#include "assert.h"

// C4B output: 1.33+0.67|[z,y]|

#include "tick.h"

void count_up(int, int);

void count_down(int x,int y)
{
	tick(1);
	if (x > y) {
		x--;
		count_up(x, y);
	}
}

void count_up(int x, int y)
{
	tick(1);
	if (y + 1 < x) {
		y += 2;
		count_down(x, y);
	}
}

void start(int y, int z) {
	count_down(y, z);
}

int main() 
{
	init_tick(0);

	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();

	start(y, z);
	
	int bnd = 4 + 2 * ((y > z) ? (y - z) : 0);
	__VERIFIER_assert(3 * __cost <= bnd);
	
	return 0;
}

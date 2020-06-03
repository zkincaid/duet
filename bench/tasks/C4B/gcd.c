#include "assert.h"

// C4B output : |[0,x]|+|[0,y]|

#include "tick.h"

int gcd(int x, int y) {

	if (x <= 0) return y;
	if (y <= 0) return x;
	for (;;) {
		tick(1);
		if (x > y) x -= y;
		else if (y > x) y -= x;
		else break;
	}
	
	return x;
}

	

int main() 
{
	init_tick(0);
	
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();	

	gcd(x, y);
	
	int mainbnd = (x > 0 ? x : 0) + ( y > 0 ? y : 0);
	__VERIFIER_assert(__cost <= mainbnd);
	return 0;
}

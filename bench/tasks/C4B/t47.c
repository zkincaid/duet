#include "assert.h"

// C4B output: 1+|[0,n]|

#include "tick.h"

void start(int n)
{
	int flag = 1;

	while (flag > 0) {
		tick(1);
		if (n > 0) {
			n--;
			flag = 1;
		} else
			flag = 0;
	}
}

int main() 
{
	init_tick(0);

	int n = __VERIFIER_nondet_int();
	
	start(n);
	
	int bnd = 1 + ((n > 0) ? n : 0);
	__VERIFIER_assert (__cost <= bnd);
	
	return 0;
}

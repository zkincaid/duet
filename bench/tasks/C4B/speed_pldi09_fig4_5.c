#include "assert.h"

// C4B output: Not Available
// SPEED output: mx(n,n-m)

#include "tick.h"

void start(int n, int m, int dir)
{
	int i;

	__VERIFIER_assume(0 < m && m < n);

	i = m;

	while (0 < i && i < n) {
		tick(1);
		if (dir == 1)
			i++;
		else
			i--;
	}
}

int main() 
{
	init_tick(0);
	
	int dir = __VERIFIER_nondet_int();
	int m = __VERIFIER_nondet_int();
	int n = __VERIFIER_nondet_int();
	
	start(n, m, dir);
	
	int bnd = (n > ( n - m)) ? n : (n - m);
	__VERIFIER_assert (__cost <= bnd);
	return 0;
}

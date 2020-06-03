#include "assert.h"

// C4B output : |[0,n]|

#include "tick.h"

void start(int n)
{
  int i;
  int j;

  i=0;
  while (i<n) {
    j=i+1;
    while (j<n) {
	  if (__VERIFIER_nondet_int()) {
        tick(1);
        j=j-1;
        n=n-1;
      }
      j=j+1;
    }
    i=i+1;
  }
}

int main() 
{
	init_tick(0);
	
	int n = __VERIFIER_nondet_int();
	start(n);
	
	int bnd = (n > 0) ? n : 0;
	__VERIFIER_assert(__cost <= bnd);
	return 0;
}

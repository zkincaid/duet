#include "assert.h"

#include "tick.h"

void sort(int arr[], int n)
{
    int i, key, j;
    for (i = 1; i < n; i++) {
		tick(1);
        key = arr[i];
        j = i - 1;
        /* Move elements of arr[0..i-1], that are
          greater than key, to one position ahead
          of their current position */
        while (j >= 0 && arr[j] > key) {
			tick(1);
            arr[j + 1] = arr[j];
            j = j - 1;
        }
        arr[j + 1] = key;
    }
}

int main() 
{
	int arr[1000];
	init_tick(0);
	
	int n = __VERIFIER_nondet_int();
	__VERIFIER_assume(n > 0);
	sort(arr, n);
	int mainbnd = (n * n);
	__VERIFIER_assert(__cost <= mainbnd);
	return 0;
}

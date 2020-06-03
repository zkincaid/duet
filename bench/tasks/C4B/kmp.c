#include "assert.h"

/* Knuth-Morris-Pratt string searching */
// C4B output: 1+2|[0,n]|

#include "tick.h"

int srch(int t[],    // object string 
         int n,      // length of the object string
         int p[],    // pattern string
         int m,      // length of pattern string
         int b[]     // backjump table ("failure function")
        )
{
       int i = 0,    // position in object string
           j = 0,    // position in pattern
           k = -1;   // backjump distance (initially undefined)
        
        while (i < n) {
	      tick(1);
              while (j >= 0 && t[i] != p[j]) {  // check for a match failure
                        tick(1);
                        // Adjust j according to the failure function
                        k = b[j];
                        __VERIFIER_assume(k > 0);
                        __VERIFIER_assume(k <= j + 1);
                        j -= k;
                }
                i++, j++;
                if (j == m)
                        break;
        }
        return i;
}

int main()
{
        init_tick(0);
        
        int t[30];       // object string (i.e., the string being searched)
        int t_len = 10;  // length of object string
        int p[20];       // pattern string
        int p_len = 5;   // length of pattern string
        int b[20];       // backjump table ("failure function")
        int i;

        // Initialize the object string
        for (i = 0; i < t_len; i++) {
            t[i] = __VERIFIER_nondet_int();
        }

        // Initialize the pattern string
        for (i = 0; i < p_len; i++) {
            p[i] = __VERIFIER_nondet_int();
        }

        // Initialize the backjump table
        for (i = 0; i < p_len; i++) {
            b[i] = __VERIFIER_nondet_int();
            __VERIFIER_assume(b[i] > 0);
            __VERIFIER_assume(b[i] <= i+1);
        }

        srch(t, t_len, p, p_len, b);

	    __VERIFIER_assert (__cost <= 2 * t_len + 1);
        return 0;
}

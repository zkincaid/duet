#include <stdlib.h>

void assert(int);

int main() {
    int *p, *q, *r;
    int havoc1, havoc2; /* uninitialized */
    p = malloc(sizeof(int));
    q = malloc(sizeof(int));

    if (havoc1) {
	r = q;
    } else {
	r = p;
    }

    *p = 0; /* doesn't reach */
    *q = 1; /* reaches */

    /* Exhibits the path-sensitivity of the analysis: along the "then" branch,
       neither *p=0 nor *q=1 can reach the read of *r at the assertion, since
       *r is overwritten.  Along the "else" branch, *p=0 can not reach the
       read of *r at the assertion because *p is overwritten.  So there is no
       path where *r reads the value of 0 from *p=0.  We can't prove that this
       dependence is spurious using the technique from Ju Qian, Baowen Xu, and
       Hongbo Min: "Interstatement Must Aliases for Data Dependence Analysis
       of Heap Locations" */
    if (havoc2) {
	*r = 1; /* reaches */
    } else {
	*p = 1; /* reaches */
    }
    assert(*r == 1);
    return 0;
}

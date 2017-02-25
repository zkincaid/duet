#include <stdlib.h>

void assert(int);

int main() {
    int *p, *q, *r, **s;
    int havoc1, havoc2; /* uninitialized */
    p = malloc(sizeof(int));
    q = malloc(sizeof(int));
    if (havoc1) {
	s = &p;
    } else {
	s = &q;
    }
    *p = 1; /* reaches */
    *q = 0; /* doesn't reach, but the analysis thinks it will */

    if (havoc2) {
	r = q;
    } else {
	r = p;
    }

    *s = q;

    *p = 2; /* reaches */
    *q = 2; /* reaches */

    assert(1 <= *r); /* safe, but the analysis thinks *q=0 reaches */
    assert(*r == 2); /* unsafe */
    return 0;
}

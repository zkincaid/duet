#include <stdlib.h>

void assert(int);

int main() {
    int *p, *q, *r;
    int havoc; /* uninitialized */
    p = malloc(sizeof(int));
    q = malloc(sizeof(int));
    *p = 0; /* doesn't reach */
    *q = 0; /* doesn't reach */
    *p = 1; /* reaches */
    *q = 1; /* reaches */
    if (havoc) {
	r = q;
    } else {
	r = p;
    }
    assert(*r == 1);
    return 0;
}

#include <stdlib.h>

void assert(int);

int main() {
    int *p, *q, *r;
    int havoc; /* uninitialized */
    p = malloc(sizeof(int));
    q = malloc(sizeof(int));
    *p = 0; /* doesn't reach */
    *q = 0; /* doesn't reach */
    if (havoc) {
	r = q;
    } else {
	r = p;
    }
    *r = *r + 1;
    assert(*r == 1);
    return 0;
}

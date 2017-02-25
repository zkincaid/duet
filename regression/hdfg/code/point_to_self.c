#include <stdlib.h>

void assert(int);

int main() {
    int *p;
    int a;
    int havoc;
    a = 0; /* reaches */
    p = (int*) &p;
    assert(p > 0); /* pass */
    *p = &a; /* doesn't reach */
    if (havoc) {
	assert(*p == 0); /* this should pass, but doesn't because we don't
			    handle must-aliasing relationships for
			    addresses. */
    } else {
	assert(p > 0); /* pass */
    }
    return 0;
}

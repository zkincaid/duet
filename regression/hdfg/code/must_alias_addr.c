#include <stdlib.h>

void assert(int);

int main() {
    int *p;
    int a;
    p = &a;
    a = 0;
    *p = 1;
    assert(a == 1); /* Can't prove this assertion, because we don't support
		       must-aliasing relationships between pointer variables
		       and addresses. */
    return 0;
}

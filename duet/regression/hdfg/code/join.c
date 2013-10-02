/* Test join nodes */
#include <stdlib.h>

void assert(int);

void foo (int *p) {
    if (*p > 0) {
	*p = 1;
    } else {
	*p = 2;
    }
}

int main() {
    int a;
    int *q = malloc(sizeof(int));
    *q = 0;
    a = 0;
    foo(&a);
    foo(q);
    assert(a < 2);  /* error */
    assert(*q < 2); /* error */
    assert(a > 1);  /* error */
    assert(*q > 1); /* error */
    assert(a > 0);  /* safe  */
    assert(*q > 0); /* safe  */
    return 0;
}

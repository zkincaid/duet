#include <stdlib.h>

void assert(int);

int foo(int x, int y) {
    assert(x > 0); /* pass */
    assert(y == 1); /* fail */
    return x + y;
}

int main() {
    int i,j,k;
    i = 1;
    j = 2;
    k = foo(i, j);
    assert(k == 3); /* pass */
    return 0;
}

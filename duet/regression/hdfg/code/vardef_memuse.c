#include <stdlib.h>

void assert(int);

int main(int argc, char* argv[]) {
    int x, y, *p, *q;
    int havoc;
    p = &x;
    x = 0;
    y = 1;
    assert(*p == 0); // pass
    if (havoc) {
	q = &x;
    } else {
	q = &y;
    }
    assert(*q == 0); // fail
    return 0;
}

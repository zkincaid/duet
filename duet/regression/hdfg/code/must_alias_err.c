#include <stdlib.h>

void assert(int);

int main() {
    int *p, *q;
    int havoc;
    p = malloc(sizeof(int));
    if (havoc) {
	q = p;
    } else {
	q = malloc(sizeof(int));
    }
    *p = 0;
    *q = 1;
    assert(*p == 0);
    return 0;
}

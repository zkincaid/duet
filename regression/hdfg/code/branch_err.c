#include <stdlib.h>

void assert(int);

int main() {
    int *p;
    int havoc;
    p = malloc(sizeof(int));
    if (havoc) {
	*p = 0;
    } else {
	*p = 1;
    }
    assert(*p == 0);
    return 0;
}

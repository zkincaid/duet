#include <stdlib.h>

int main() {
    int *p, *q, *r;
    p = malloc(sizeof(int)*10);
    while (*p) {
	p = p + 1;
    }
    return 0;
}

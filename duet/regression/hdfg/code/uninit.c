#include <stdlib.h>

void assert(int);

int main() {
    int *p;
    int havoc1,havoc2;
    int uninit_var;
    p = malloc(sizeof(int));
    if (havoc1) {
	*p = 0;
    } else {
	uninit_var = 0;
    }
    if (havoc2) {
	assert(*p == 0); /* may be uninitialized */
    } else {
	assert(uninit_var == 0); /* may be uninitialized */
    }
    return 0;
}

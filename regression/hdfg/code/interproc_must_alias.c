#include <stdlib.h>

void assert(int);

void foo(int* param) {
    *param = *param + 1;
    return;
}

int main() {
    int *loc;
    loc = malloc(sizeof(int));
    *loc = 0;
    foo(loc);
    assert(*loc == 1);
    return 0;
}

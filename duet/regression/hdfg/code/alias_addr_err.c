#include <stdlib.h>

void assert(int);

int main() {
    int *p;
    int havoc;
    int a;
    p = &a;
    a = 0;
    *p = 1;
    assert(a == 0);
    return 0;
}

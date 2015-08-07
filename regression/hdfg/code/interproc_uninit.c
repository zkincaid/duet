#include <stdlib.h>

void assert(int);

int global;

int foo(int x) {
    int local, uninit_local;
    if (x < 0) {
	uninit_local = 0;
	local = 0;
    } else {
	local = 1;
    }
    assert(global == 0); /* fail */
    global = 1;
    assert(local >= 0); /* pass */
    assert(uninit_local == 0); /* fail */
    return 0;
}

int main() {
    int local;
    foo(local);
    assert(global == 1); /* pass */
    return 0;
}

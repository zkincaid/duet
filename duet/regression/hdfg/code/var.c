#include <stdlib.h>

void assert(int);

int global;

int main() {
    int x, havoc;
    x = 0;
    x = x + 1; /* variable writes should always be strong upates */
    assert(x == 1);

    global = 0;
    if (havoc) {
	global = 1;
    } else {
	global = 2;
    }
    assert(global > 0);
    return 0;
}

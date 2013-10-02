#include <stdio.h>
#include <stdlib.h>

void assert(int);

int main(int argc, char *argv) {
    int i,j;
    FILE *file;

    file = fopen(argv[0], "r");
    if (file > 0) {
	assert(file > 0);
    }
    return 0;
}

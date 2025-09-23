#include <stdlib.h>

void f(int count) {
    int* curr = malloc (2 * sizeof(int));
    int* next;
    while (count > 0) {
        count --;
        next = malloc (2 * sizeof(int));
        next[0] = 2;
        free(curr);
        curr = next;
    }
    curr[0] = 1;
} 
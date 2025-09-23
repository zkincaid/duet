#include <stdlib.h>

int f(int x, int y) {
    int a = y + 1;
    int c = x + a;
    int b = y + 4;
    int d = x + b;
    
    int *arr = (int *)malloc(3 * sizeof(int));
    arr[0] = a;
    arr[1] = b;
    arr[2] = x;
    free(arr);
    
    while (c < 10) {
        c = c + 1;
    }
    return 0;
}
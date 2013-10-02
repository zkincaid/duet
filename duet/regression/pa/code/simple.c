#include <stdlib.h>
void main () {
    int x, y;
    int *p, *q, *r;
    p = &x;
    q = &y;
    q = p;
    p = malloc(sizeof(int)); /* alloc1 */
    r = q;
    r = malloc(sizeof(int)); /* alloc2 */
}

/*
  p -> {alloc1, &x}
  q -> {alloc1, &x, &y}
  r -> {alloc1, alloc2, &x, &y}
*/

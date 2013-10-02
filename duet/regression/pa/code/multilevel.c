#include <stdlib.h>
void main () {
    int x, y, z;
    int *p, *q, *r;
    int **a, **b, **c;
    a = &p;
    b = &q;
    p = &x;
    q = &y;
    *a = &z;
    *b = *a;
    r = *a;
    c = &q;
    c = &r;
    *c = malloc(sizeof(int*));
}

/*
  p -> {&x, &z}
  q -> {alloc#14, &x, &y, &z}
  r -> {alloc#14, &x, &z}
  a -> {&p}
  b -> {&q}
  c -> {&q, &r}
*/

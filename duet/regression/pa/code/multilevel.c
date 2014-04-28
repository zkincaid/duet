#include <stdlib.h>
void main () {
    int x, y, z;
    int *p, *q, *r;
    int **a, **b, **c;
    int *m;
    a = &p;
    b = &q;
    p = &x;
    q = &y;
    *a = &z;
    *b = *a;
    r = *a;
    c = &q;
    c = &r;
    m = malloc(sizeof(int*));
    *c = m;

    switch(rand()) {
    case 0: assert(p != &x); // fail
    case 1: assert(p != &z); // fail

    case 2: assert(q != m); // fail
    case 3: assert(q != &x); // fail
    case 4: assert(q != &y); // fail
    case 5: assert(q != &z); // fail

    case 6: assert(r != m); // fail
    case 7: assert(r != &x); // fail
    case 8: assert(r != &z); // fail

    case 9: assert(a != &p); // fail

    case 10: assert(b != &q); // fail

    case 11: assert(c != &q); // fail
    default: assert(c != &r); // fail
    }
}

/*
  p -> {&x, &z}
  q -> {alloc#14, &x, &y, &z}
  r -> {alloc#14, &x, &z}
  a -> {&p}
  b -> {&q}
  c -> {&q, &r}
*/

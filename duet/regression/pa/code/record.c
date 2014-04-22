#include <stdlib.h>

struct foo_t {
    int *p;
    int *q;
};

int main () {
    struct foo_t x, y;
    struct foo_t *r;
    int z;

    x.p = (int *) &(y.p);
    x.q = (int *) &(y.q);
    r = &x;
    r->p = &z;    /* writes to x.p */
    *(r->q) = &z; /* writes to y.q */

    switch(rand()){
    case 0: assert(x.p != &y.p); // fail
    case 1: assert(x.p != &y.q); // pass
    case 2: assert(x.q != &y.p); // pass
    case 3: assert(x.q != &y.q); // fail

    case 4: assert(y.p != &z); // pass
    case 5: assert(y.q != &z); // fail

    case 6: assert(r != &x); // fail
    case 7: assert(r != &x.p); // fail
    default: assert(r != &x.q); // pass
    }
    return 0;
}

/*
  x.p -> {&y.p}
  x.q -> {&y.q}
  y.p -> {}
  y.q -> {&z}
  r -> {&x}
 */

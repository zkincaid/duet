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
    return 0;
}

/*
  x.p -> {&y.p}
  x.q -> {&y.q}
  y.p -> {}
  y.q -> {&z}
  r -> {&x}
 */

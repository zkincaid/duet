#include <stdlib.h>

struct Type1 {
    int f1;
    struct Type1 *f2;
};

struct Type2 {
    int f3;
    struct Type2 *f4;
};

int main() {
    struct Type1 *p;
    struct Type2 *q;
    struct Type1 *tmp1;
    struct Type2 *tmp2;
    p = malloc(sizeof(struct Type1)); /* memloc1 */
    q = malloc(sizeof(struct Type2)); /* memloc2 */

    p->f2 = (struct Type1*) q;
    tmp1 = p->f2;

    tmp1->f2 = (struct Type1*) p;

    tmp2 = q->f4; /* tmp2 can point to memloc1, since tmp1->f2 overlaps q->f4 */

    switch(rand()) {
    case 0: assert(tmp2 != p); // fail
    case 1: assert(tmp1 != q); // fail
    case 2: assert(p->f2 != q); // fail
    default: assert(q->f4 != p); // fail
    }
    return 0;
}

/*
  p -> {memloc1}
  q -> {memloc2}
  memloc1.f2 -> {memloc2}
  tmp1 -> {memloc2}
  memloc2.f2 -> {memloc1}
  tmp2 -> {memloc1}
 */

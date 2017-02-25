#include <stdlib.h>
void main () {
    int x, y;
    int *p, *q, *r;
    int *a1, *a2;
    p = &x;
    q = &y;
    q = p;
    p = a1 = malloc(sizeof(int)); /* alloc1 */
    r = q;
    r = a2 = malloc(sizeof(int)); /* alloc2 */

    switch(rand()){
    case 0: assert(p != a1); // fail
    case 1: assert(p != &x); // fail

    case 2: assert(q != a1); // fail
    case 3: assert(q != &x); // fail
    case 4: assert(q != &y); // fail

    case 5: assert(r != a1); // fail
    case 6: assert(r != a2); // fail
    case 7: assert(r != &x); // fail
    default: assert(r != &y); // fail
    }
}

/*
  p -> {alloc1, &x}
  q -> {alloc1, &x, &y}
  r -> {alloc1, alloc2, &x, &y}
*/

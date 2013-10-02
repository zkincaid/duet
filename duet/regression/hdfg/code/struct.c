#include <stdlib.h>

void assert(int);

struct List {
    int data;
    struct List *next;
};

struct List g;

int main() {
    struct List *p, *q;
    p = malloc(sizeof(struct List));
    q = p;
    p->data = 0;
    q->data ++;
    assert(p->data == 1); /* pass */
    assert(p->next == 0); /* fails (uninitialized) */

    g.next = p;
    assert(g.next->data == 1); /* pass */
    assert(g.data == 0); /* fails (uninitialized) */
    return 0;
}

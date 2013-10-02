#include <stdlib.h>

struct List {
    int data;
    struct List *next;
};

struct List g;

int main() {
    struct List *p, *q, *curr;
    p = malloc(sizeof(struct List));
    q = malloc(sizeof(struct List));
    q->next = &g;
    q->data = 0;
    p->next = q;
    p->data = 1;

    g.next = p;
    g.data = 2;
    curr = g.next;
    while (curr != &g) {
	curr = curr->next;
    }

    return 0;
}

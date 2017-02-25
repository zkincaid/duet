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
	switch(rand()) {
	case 1: assert (curr != p); // fail
	default: assert (curr != q); // fail
	}
    }

    switch(rand()) {
    case 0: assert (p != q); // pass

    case 1: assert (q->next != &g); // fail
    case 2: assert (q->next != p); // pass
    case 3: assert (q->next != q); // pass

    case 4: assert (p->next != &g); // pass
    case 5: assert (p->next != p); // pass
    case 6: assert (p->next != q); // fail

    default: assert (curr != &g); // fail
    }

    return 0;
}

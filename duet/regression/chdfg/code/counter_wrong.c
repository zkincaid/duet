#include <pthread.h>

#define MAX 10

struct counter {
    pthread_mutex_t lock;
    int counter;
};

struct counter *alloc_counter() {
    struct counter *c;
    c = malloc(sizeof(struct counter));
    c->counter = 0;
    return c;
}

void inc(struct counter *c) {
    pthread_mutex_lock(&(c->lock));
    assert(c->counter <= MAX);
    assert(c->counter >= 0);
    if (c->counter < MAX) {
	c->counter++;
    }
    pthread_mutex_unlock(&(c->lock));
}

void dec(struct counter *c) {
    assert(c->counter <= MAX);
    assert(c->counter >= 0);
    if (c->counter > 0) {
	c->counter--;
    }
}

void main() {
    struct counter *c;

    pthread_t t;
    int n;
    c = alloc_counter();
    while(n > 0) {
	switch(rand()) {
	case 0:
	    pthread_create(&t, NULL, inc, c);
	    break;
	case 1:
	    pthread_create(&t, NULL, dec, c);
	    break;
	default:
	    break;
	}
	n--;
    }
}

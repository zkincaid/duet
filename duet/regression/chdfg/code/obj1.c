#include <pthread.h>

struct obj {
    pthread_mutex_t lock;
    int contents;
};

void t1(struct obj *o) {
    pthread_mutex_lock(&(o->lock));
    assert(o->contents == 0); // unsafe
    o->contents = 1;
    assert(o->contents == 1); // safe
    pthread_mutex_unlock(&(o->lock));
}
void t2(struct obj *o) {
    pthread_mutex_lock(&(o->lock));
    o->contents = 2;
    pthread_mutex_unlock(&(o->lock));
}

void main() {
    pthread_t th1, th2;
    struct counter *o;
    o = malloc(sizeof(struct obj));
    pthread_create(&th1, NULL, t1, o);
    pthread_create(&th2, NULL, t2, o);
}

#include <pthread.h>

// Aliased locks actually get released

pthread_mutex_t * lock;

struct data {
  pthread_mutex_t lock;
  int something;
};

void baz() {
  pthread_mutex_unlock(lock);
}

void foo(struct data * d) {
  pthread_mutex_lock(&d->lock);
    d->something = 0;
    assert(d->something == 0); // pass
    baz();
    assert(d->something == 0); // fail
  pthread_mutex_unlock(&d->lock);
}

void bar(struct data * d) {
  lock = &d->lock;

  pthread_mutex_lock(&d->lock);
    d->something = 1;
    assert(d->something == 1); // pass
  pthread_mutex_unlock(&d->lock);
}

int main() {
  pthread_t t[2];
  struct data *d = malloc(sizeof(struct data));

  pthread_create(t, NULL, foo, d);
  pthread_create(t + 1, NULL, bar, d);

  return 0;
}

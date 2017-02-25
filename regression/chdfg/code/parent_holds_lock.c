#include <pthread.h>

// Test to make sure children don't inherit locks

int *x;
pthread_mutex_t lock;

void foo() {
  pthread_mutex_lock(&lock);
  *x = 0;
  assert(*x == 0); // fail
  pthread_mutex_unlock(&lock);
}

void bar() {
  *x = 1;
  assert(*x == 1); // fail
}

void main() {
  pthread_t t[2];

  x = malloc(sizeof(int));
  pthread_mutex_lock(&lock);
  pthread_create(t, NULL, foo, NULL);
  pthread_create(t + 1, NULL, bar, NULL);
}

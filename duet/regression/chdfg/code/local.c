#include <pthread.h>

// aliased local variables create data edges

int x;

void foo() {
  x = 0;
  assert(x == 0);
}

void bar() {
  int * local;
  local = &x;
  *local = 1;
  assert(*local == 1);
}

void main() {
  pthread_t t[2];

  pthread_create(t, NULL, foo, NULL);
  pthread_create(t+1, NULL, bar, NULL);
}


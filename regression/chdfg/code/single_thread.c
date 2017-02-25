#include <pthread.h>

int *x;
int *y;

void foo() {
  int z = *x;
  *x = *x + 1;
  assert (z == *x - 1); // pass
}

void bar() {
  int z = *y;
  *y = *y + 1;
  assert (z == *y - 1); // fail
}

int main() {
  pthread_t t;
  x = malloc(sizeof(int));
  y = malloc(sizeof(int));

  *x = 0;
  assert(*x == 0);  // pass

  pthread_create(&t, NULL, foo, NULL);
  for (int i = 0; i < 10; i++) pthread_create(&t, NULL, bar, NULL);
  return 0;
}

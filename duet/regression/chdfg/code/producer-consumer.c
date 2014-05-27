#include <pthread.h>

int NUM_THREADS;
int SIZE;
char * buffer;
int count, head, tail;
pthread_mutex_t l;

void put(char c) {
  pthread_mutex_lock(&l);
  while (count >= SIZE) {
    pthread_mutex_unlock(&l);
    pthread_mutex_lock(&l);
  }
  assert(count < SIZE); // pass
  count++;
  assert(head < SIZE);
  buffer[head] = c;
  head++;
  if (head >= SIZE) {
    head = 0;
  }
  pthread_mutex_unlock(&l);
}

char get() {
  char c;
  pthread_mutex_lock(&l);
  while (count <= 0) {
    pthread_mutex_unlock(&l);
    pthread_mutex_lock(&l);
  }
  assert(count > 0); // pass
  count--;
  assert(tail < SIZE);
  c = buffer[tail];
  tail++;
  if (tail >= SIZE) {
    tail = 0;
  }
  pthread_mutex_unlock(&l);
  return c;
}

void printf(char x) { }

void foo() {
  int i;
  for (i = 0; i < 256; i++) {
    put((char)i);
  }
}

void bar() {
  int i;
  char j;
  for (i = 0; i < 256; i++) {
    j = get();
    printf(j);
  }
}

int main() {
  int i;
  pthread_t * s = malloc(sizeof(pthread_t)*(NUM_THREADS / 2));
  pthread_t * t = malloc(sizeof(pthread_t)*(NUM_THREADS / 2));
  buffer = malloc(sizeof(char)*SIZE);

  SIZE = 50;
  count = 0;
  head = 0;
  tail = 0;

  for (i = 0; i < NUM_THREADS; i++) {
    pthread_create(s + i, NULL, foo, NULL);
    pthread_create(t + i, NULL, bar, NULL);
  }

  return 0;
}


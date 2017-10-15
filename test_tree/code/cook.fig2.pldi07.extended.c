#include <pthread.h>

int lock=0;
int x;

void* thread1(void* arg) {
  int t;
  acquire(lock);
  while (x>0) {
    t = x-1;
    x = t;
  }
  release(lock);
  return NULL;
}

void* thread2(void* arg) {
  int NONDET;
  while (NONDET) {
    acquire(lock);
    x = NONDET;
    release(lock);
  }
  return NULL;
}

void main() {
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}

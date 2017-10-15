#include <pthread.h>

int lock=0;
int x;

#define acquire_thread_id(tid, l) \
  { __blockattribute__((atomic)) \
    assume(l==0); \
    l = tid; \
  } \

void* thread1(void* arg) {
  acquire_thread_id(1, lock); // lock=0 /\ lock'=1 
  while (x>0) {
    x = x-1;
  }
  release(lock);
  return NULL;
}

void* thread2(void* arg) {
  int NONDET;
  while (NONDET) {
    acquire_thread_id(2, lock); // lock=0 /\ lock'=2 
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

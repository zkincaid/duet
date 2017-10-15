#include<pthread.h>

int x=1, m=0;

#define acquire_thread_id(tid, l) \
  { __blockattribute__((atomic)) \
    assume(l==0); \
    l = tid; \
  } \

void* thr1(void* arg) {
  acquire_thread_id(1, m); // m=0 /\ m'=1
  x = 0;
  x = 1;
  assert(x>=1);
  release(m);
  return NULL;
}

void* thr2(void* arg) {
  acquire_thread_id(2, m); // m=0 /\ m'=2
  x = 0;
  x = 1;
  assert(x>=1);
  release(m);
  return NULL;
}

void main(){
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thr1, NULL);
  pthread_create(&t2, NULL, thr2, NULL);
}

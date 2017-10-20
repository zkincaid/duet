#include<pthread.h>

int x=1, m=0;

#define acquire(l) \
  __VERIFIER_atomic_begin(); \
  assume (l == 0); \
  l = 1; \
  __VERIFIER_atomic_end()

#define release(l) \
  __VERIFIER_atomic_begin(); \
  assert (l == 1); \
  l = 0; \
  __VERIFIER_atomic_end()

void* thr(void* arg) {
  acquire(m); // m=0 /\ m'=1
  x = 0;
  x = 1;
  assert(x>=1);
  release(m);
  return NULL;
}

void main(){
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thr, NULL);
  pthread_create(&t2, NULL, thr, NULL);

}

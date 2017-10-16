#include<pthread.h>

int x=1, m=0;

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

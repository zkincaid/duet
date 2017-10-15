#include<pthread.h>

int x=1, m=0;

void* thr(void* arg) {
  int l=1;
  acquire(m); // m=0 /\ m'=1
  if (l>=2) { x=0; }
  else { x=1; }
  assert(x>=1);
  release(m);
  return NULL;
}

void main(){
  pthread_t t1;

  pthread_create(&t1, NULL, thr, NULL);
}

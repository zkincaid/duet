#include<pthread.h>
int g;
int n;

void* thr(void* arg) {
  int junk = 0;
  g = 0;
  junk++;
  junk++;
  junk++;
  g++;
  junk++;
  junk++;
  assert(g <= n);
  junk++;
  junk++;
  junk++;
  junk++;
  junk++;
  return NULL;
}

void main(){
  pthread_t t;

  int nondet;
  n = nondet;
  for (int i = 0; i < n; ++i){
    pthread_create(&t, NULL, thr, NULL);
  }
}

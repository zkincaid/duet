#include<pthread.h>
int g;

void* thr(void* arg) {
  int junk = 0;
  g = 0;
  junk++;
  junk++;
  junk++;
  g++;
  junk++;
  junk++;
  assert(g <=2);
  junk++;
  junk++;
  junk++;
  junk++;
  junk++;
  return NULL;
}

void main(){
  pthread_t t;

  pthread_create(&t, NULL, thr, NULL);
}

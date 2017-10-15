#include <pthread.h>

int x=1;
int y=0;

void* thread1(void* arg) {
  while (x=1) {
    y = y+1;
  }
  while (y>0) {
    y = y-1;
  }
  return NULL;
}

void* thread2(void* arg) {
  x = 0;
  return NULL;
}

void main() {
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}

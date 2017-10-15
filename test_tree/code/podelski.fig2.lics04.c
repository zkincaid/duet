#include <pthread.h>

int x, y;

void* thread1(void* arg) {
  while (x>0 && y>0) {
    { __blockattribute__((atomic))
      x = x-1;
      y = x;
    } 
  }
  return NULL;
}

void* thread2(void* arg) {
  while (x>0 && y>0) {
    { __blockattribute__((atomic))
      x = y-2;
      y = x+1;
    } 
  }
  return NULL;
}

void main() {
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}

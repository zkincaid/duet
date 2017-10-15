#include <pthread.h>

int t1=0, t2=0; // N natural-number tickets
int x; // variable to test mutual exclusion

void* thread1(void* arg) {
  while (1) {
    t1 = t2 + 1;
    while( t1 >= t2 && ( t2 > 0 ) ) {}; // condition to exit the loop is (t1<t2 \/ t2=0)
    x=0;
    assert(x <= 0);
    t1 = 0;
  }
  return NULL;
}

void* thread2(void* arg) {
  while (1) {
    t2 = t1 + 1;
    while( t2 >= t1 && ( t1 > 0 ) ) {}; // condition to exit the loop is (t2<t1 \/ t1=0)
    x = 1;
    assert(x >= 1);
    t2 = 0;
  }
  return NULL;
}

void main() {
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}

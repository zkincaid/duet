#include <pthread.h>

int t1=0, t2=0; // N integer tickets
int x; // variable to test mutual exclusion

void* thread1(void* arg) {
  int __temp_1__;
  while (1) {
    __temp_1__ = t2;
    t1 = __temp_1__ + 1;
    __temp_1__ = t2;
    while( t1 >= __temp_1__ && ( __temp_1__ > 0 ) ) {
      __temp_1__ = t2;
    }; // condition to exit the loop is (t1<t2 \/ t2=0)
    x = 0;
    assert(x <= 0);
    t1 = 0;
  }
  return NULL;
}

void* thread2(void* arg) {
  int __temp_2__;
  while (1) {
    __temp_2__ = t1;
    t2 = __temp_2__ + 1;
    __temp_2__ = t1;
    while( t2 >= __temp_2__ && ( __temp_2__ > 0 ) ) {
      __temp_2__ = t1;
    }; // condition to exit the loop is (t2<t1 \/ t1=0)
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

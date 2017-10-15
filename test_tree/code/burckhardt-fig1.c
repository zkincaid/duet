#include <pthread.h> 

#define false 0
#define true 1

int B = 0;
int X = 0;
int Y = 0;

void* thread1(void* arg) {
  int r = B;
  if (r) {
    X = r; 
    if (r) { Y = 0; } else { Y = 1; } // Y = !r;
  } else {
    if (r) { Y = 0; } else { Y = 1; } // Y = !r; 
    X = r;
  }
  return NULL;
}

void* thread2(void* arg) { // optimized version of thr1
  int r = B;
  X = r;
  if (r) { Y = 0; } else { Y = 1; } // Y = !r;
  return NULL;
}

void* thread3(void* arg) {
  X = 1;
  assert(X || Y);
  return NULL;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, NULL, thread1, NULL);
  // pthread_create(&t1, NULL, thr2, NULL);
  pthread_create(&t2, NULL, thread3, NULL); 
  return 0;
}

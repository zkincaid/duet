#include <pthread.h>

int w, r, x, y;

void* thread1(void* arg) { //writer
  glb_init(w==0);
  glb_init(r==0);
  { __VERIFIER_atomic_begin();
    assume(w==0);
    assume(r==0);
    w = 1;
    __VERIFIER_atomic_end();
  }
  x = 3;
  w = 0;
  return NULL;
}

void* thread2(void* arg) { //reader
  { __VERIFIER_atomic_begin();
    assume(w==0);
    r = r+1;
    __VERIFIER_atomic_end();
  }
  y = x;
  assert(y == x);
  r = r-1;
  return NULL;
}

void main(){
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}

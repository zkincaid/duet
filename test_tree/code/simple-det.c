#include<pthread.h>

int x=0, m=0;
int can_start = 0;
int done = 0;

void* thr1(void* arg) {
  { __blockattribute__((atomic))
    can_start = can_start - 1;
    assume(can_start >= 0);
  }
  acquire(m); // m=0 /\ m'=1
  x = 2;
  release(m);
  done = done + 1;
  return NULL;
}

void* thr2(void* arg) {
  { __blockattribute__((atomic))
    can_start = can_start - 1;
    assume(can_start >= 0);
  }
  acquire(m); // m=0 /\ m'=1
  if (x == 0) { x = x + 2; }
  release(m);
  done = done + 1;
  return NULL;
}

void main() {
  pthread_t t1, t2;
  
  int x_out_1;
  int x_in_1 = x;
  can_start = 2; // fork thr1(); fork thr2();
  pthread_create(&t1, NULL, thr1, NULL);
  pthread_create(&t2, NULL, thr2, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  assume(done >= 2); // join
  x_out_1 = x;
  x = x_in_1;
  can_start = 2; // fork thr1(); fork thr2();
  pthread_create(&t1, NULL, thr1, NULL);
  pthread_create(&t2, NULL, thr2, NULL);
  pthread_join(t1, NULL);
  pthread_join(t2, NULL);
  assume(done >= 4); // join
  assert(x_out_1 == x);
}


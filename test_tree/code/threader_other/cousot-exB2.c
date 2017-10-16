#include <pthread.h>

int n;
int p1, p2;
int done;

void* thread1(void* arg) {
  p1 = 1;
  while (n > 1) {
    { __blockattribute__((atomic))
      n = n - 1; 
      p1 = 2 * p1;
    }
  }
  done++;
  return NULL;
}

void* thread2(void* arg) {
  p2 = 1;
  while (n > 1) {
    { __blockattribute__((atomic))
      n = n - 1;
      p2 = 2 * p2;
    }
  }
  done++;
  return NULL;
}

void main() { // the parallel program computes 2^n when n >= 0 (11 transitions)
  int p;
  glb_init(n >= 0);
  glb_init(done == 0);

  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
  
  if (done >= 2) {
    if (n == 0) {
      p = p1 * p2;
    } else {
      p = 2 * p1 * p2;
    }
    // proves that n \in {0,1}
    assert(n >= 0); assert(n <= 1);
  }
}

void main_smaller() { // same as main(), but frontend produces only 8 transitions
  int p; 
  int NONDET;
  glb_init(n >= 0);
  glb_init(done == 0);
  if (done >= 2) {
    if (NONDET) {
      { __blockattribute__((atomic))
	assume(n == 0);
	p = p1*p2;
      }
    } else {
      { __blockattribute__((atomic))
	assume(n != 0);
	p = 2*p1*p2;
      }
    }
    // proves that n \in {0,1}
    { __blockattribute__((atomic))
      assert(n >= 0);
      assert(n <= 1);
    }
  }
}


/* core program that has a non-thread-modular proof:

void main() { 
  glb_init(n >= 0);
  glb_init(done == 0);
  if (done >= 2) {
    assert(n >= 0);
  }
}

void thr1() {
  while (n > 1) {
      n = n - 1; 
  }
  done++;
}

void thr2() {
  while (n > 1) {
      n = n - 1;
  }
  done++;
}

*/

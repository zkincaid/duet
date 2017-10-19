// #include <assert.h> //CP: gcc preprocessor inlines the assert
#include <pthread.h>

int idx; // bit idx = 0; controls which of the two elements ctr1 or ctr2 will be used by readers
int ctr1, ctr2; // byte ctr[2];
int readerprogress1, readerprogress2; // byte readerprogress[N_QRCU_READERS];
int mutex; // bit mutex = 0; updates are done in critical section, only one writer at a time
int NONDET;

#define acquire(l) \
  __VERIFIER_atomic_begin(); \
  assume (l == 0); \
  l = 1; \
  __VERIFIER_atomic_end()

#define release(l) \
  __VERIFIER_atomic_begin(); \
  assert (l == 1); \
  l = 0; \
  __VERIFIER_atomic_end()

void* qrcu_reader1(void* arg) {
  int myidx;
  
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (NONDET) {
      { __VERIFIER_atomic_begin();
	assume(myidx <= 0);
	assume(ctr1>0);
	ctr1++;
	__VERIFIER_atomic_end();
      }
      break;
    } else {
      if (NONDET) {
	{ __VERIFIER_atomic_begin();
	  assume(myidx > 0);
	  assume(ctr2>0);
	  ctr2++;
          __VERIFIER_atomic_end();
	}
	break;
      } else {}
    }
  }
  /* This is a simpler code for rcu_read_lock, but the frontend generates too many transitions
  while (1) {
    myidx = idx;
    if (myidx <= 0 && ctr1>0) {
      ctr1++; break;
    } else {
      if (myidx > 0 && ctr2>0) {
	ctr2++; break;
      } else {}
    }
    } */

  readerprogress1 = 1; /*** readerprogress[me] = 1; ***/
  readerprogress1 = 2; /*** readerprogress[me] = 2 ***/

  /* rcu_read_unlock */
  { __VERIFIER_atomic_begin();
      if (myidx <= 0) { ctr1--; } // use ctr1
      else { ctr2--; } // use ctr2
    __VERIFIER_atomic_end();
  }
  return NULL;
}

/* sums the pair of counters forcing weak memory ordering */
#define sum_unordered \
  if (NONDET) {       \
    sum = ctr1;       \
    sum = sum + ctr2; \
  } else {            \
    sum = ctr2;       \
    sum = sum + ctr1; \
  }

void* qrcu_updater(void* arg) {
  int i;
  int readerstart1;
  int readerstart2;
  int sum;

  glb_init(idx==0);
  glb_init(ctr1==1);
  glb_init(ctr2==0);
  glb_init(readerprogress1==0);
  glb_init(readerprogress2==0);
  glb_init(mutex==0);  

  /* Snapshot reader state. */
  { __VERIFIER_atomic_begin();
      readerstart1 = readerprogress1;
      readerstart2 = readerprogress2;
    __VERIFIER_atomic_end();
  }

  sum_unordered;
  if (sum <= 1) { sum_unordered; }
  if (sum > 1) {
    acquire(mutex);
    if (idx <= 0) { ctr2++; idx = 1; ctr1--; }
    else { ctr1++; idx = 0; ctr2--; }
    if (idx <= 0) { while (ctr2 > 0); }
    else { while (ctr1 > 0); }
    release(mutex);
  }

  /* Verify reader progress. */
  { __VERIFIER_atomic_begin();
      if (NONDET) {
	assume(readerstart1 == 1);
	assume(readerprogress1 == 1);
	assert(0);
      } else {
	if (NONDET) {
	  assume(readerstart2 == 1);
	  assume(readerprogress2 == 1);
	  assert(0);
	} else { }
      }
    __VERIFIER_atomic_end();
  }
  /* Frontend generates too many transitions:
  { __blockattribute__((atomic))
      sum = 0;
      if (readerstart1 == 1 && readerprogress1 == 1)
	sum++;
      if (readerstart2 == 1 && readerprogress2 == 1)
	sum++;
      assert(sum == 0);
      } */

  return NULL;
}

void* qrcu_reader2(void* arg) {
  int myidx;
  
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (NONDET) {
      { __VERIFIER_atomic_begin();
	assume(myidx <= 0);
	assume(ctr1>0);
	ctr1++;
        __VERIFIER_atomic_end();
      }
      break;
    } else {
      if (NONDET) {
	{ __VERIFIER_atomic_begin();
	  assume(myidx > 0);
	  assume(ctr2>0);
	  ctr2++;
          __VERIFIER_atomic_end();
	}
	break;
      } else {}
    }
  }

  readerprogress2 = 1; /*** readerprogress[me] = 1; ***/
  readerprogress2 = 2; /*** readerprogress[me] = 2 ***/

  /* rcu_read_unlock */
  { __VERIFIER_atomic_begin();
      if (myidx <= 0) { ctr1--; } // use ctr1
      else { ctr2--; } // use ctr2
    __VERIFIER_atomic_end();
  }
  return NULL;
}

#define acquire_thread_id(tid, l) \
  { __VERIFIER_atomic_begin(); \
    assume(l==0); \
    l = tid; \
    __VERIFIER_atomic_end(); \
  }

void main() {
  pthread_t t1, t2, t3;

  pthread_create(&t1, NULL, qrcu_reader1, NULL);
  //pthread_create(&t2, NULL, qrcu_reader2, NULL);
  pthread_create(&t3, NULL, qrcu_updater, NULL);
}

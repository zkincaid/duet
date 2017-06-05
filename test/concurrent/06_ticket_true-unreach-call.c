extern void __VERIFIER_assume(int);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_atomic_begin();
extern void __VERIFIER_atomic_end();

//Ticket lock with proportional backoff
//
//From Algorithms for Scalable Synchronization on Shared-Memory Multiprocessors, 1991 (Fig. 2).
//Also available as pseudo-code here: http://www.cs.rochester.edu/research/synchronization/pseudocode/ss.html#ticket

#include <pthread.h>

#define assume(e) __VERIFIER_assume(e)
#define assert(e) { if(!(e)) { ERROR: __VERIFIER_error();(void)0; } }

volatile unsigned next_ticket = 0;
volatile unsigned now_serving = 0;

void acquire_lock(){
	unsigned my_ticket; 

        __VERIFIER_atomic_begin();
	my_ticket = next_ticket;
	next_ticket = next_ticket + 1;
	__VERIFIER_atomic_end();

	while (my_ticket != now_serving) {
	    // spin
	}

	return;
}

void release_lock(){
    now_serving++;
}

int c = 0;
void* thr1(void* arg){
	acquire_lock();
	c++;
	assert(c == 1);
	c--;
	release_lock();

  return 0;
}

int main(){
  pthread_t t;

  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr1, 0);
  pthread_create(&t, 0, thr1, 0);
}


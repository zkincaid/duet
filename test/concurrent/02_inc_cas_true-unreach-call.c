extern void __VERIFIER_error() __attribute__ ((__noreturn__));

//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#include <pthread.h>

#define assert(e) { if(!(e)) { ERROR: __VERIFIER_error();(void)0; } }

volatile unsigned value;

void* thr1(void* arg) {
	unsigned v,vn,casret;

	do {
		v = value;

		if(v == 0u-1) {
			return 0;
		}

		vn = v + 1;

		__VERIFIER_atomic_begin(); // CAS
		if (value == v) {
		    value = vn;
		    casret = 1;
		} else {
		    casret = 0;
		}
		__VERIFIER_atomic_end();
	}
	while (casret==0);
	assert(value > v);

	return 0;
}

int main(){
    pthread_t t;
    pthread_create(&t, 0, thr1, 0);
    pthread_create(&t, 0, thr1, 0);
    pthread_create(&t, 0, thr1, 0);
    //while(1) { pthread_create(&t, 0, thr1, 0); }
}


// from chdfg test suite -- uncovered a bug in coarsen

#include <pthread.h>

// xij : flow from ti to tj
int x12;
int x13;
int x21;
int x23;
int x31;
int x32;

int y;
int z;

void assert(int);

void t1() {
    assert(z == 0); // pass
    x12 = 1;
    x13 = 1;

    x21 = 0;
    x31 = 0;
    assert(x21 == 0); // fail
    assert(x31 == 0); // fail
}

void t2() {
    assert(z == 0); // pass

    x21 = 1;
    x23 = 1;

    x12 = 0;
    x32 = 0;
    assert(x12 == 0); // fail
    assert(x32 == 0); // fail
}

void t3() {
    assert(z == 0); // pass

    x31 = 1;
    x32 = 1;

    x13 = 0;
    x23 = 0;
    assert(x13 == 0); // fail
    assert(x23 == 0); // fail
}

void main() {
    pthread_t t;
    z = 0;
    {
	// inline foo
	pthread_t t;
	pthread_create(&t, NULL, t1, NULL);
	{
	    // inline bar
	    pthread_t t;
	    pthread_create(&t, NULL, t2, NULL);
	    z = 0;
	}
    }

    pthread_create(&t, NULL, t3, NULL);
}

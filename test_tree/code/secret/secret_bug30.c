#include <pthread.h>

int to;
int from;

#define N 30
void* thread(void *arg) {
    int m;
    m = to;
    to = 0;

    from = m;

    return NULL;
}

void main() {
    pthread_t t;
    int secret;

    while(__VERIFIER_nondet_int()) {
	from = 0;
	secret = __VERIFIER_nondet_int();
	__VERIFIER_assume(secret > 0);
	
	for(int i = 0; i < N; i++) {
	    to = secret;
	    pthread_create(&t, NULL, thread, NULL);
	    __VERIFIER_assume(to == 0);
	}
	if(from > 0) {
	    assert(from == secret);
	}
    }
}

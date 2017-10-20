#include <pthread.h>

int to;
int from;

void* thread(void *arg) {
    int m;
    m = to;
    to = 0;

    from = m;

    return NULL;
}

void main() {
    pthread_t t;
    int secret = __VERIFIER_nondet_int();
    __VERIFIER_assume(secret > 0);

    from = 0;
    while(__VERIFIER_nondet_int()) {
	to = secret;
	pthread_create(&t, NULL, thread, NULL);
	__VERIFIER_assume(to == 0);
    }

    if(from > 0) {
	assert(from == secret);
    }
}

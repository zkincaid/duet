#include <pthread.h>

int len;
int *tasks;
int next;
pthread_mutex_t lock;

void* thread(void *arg) {
    int c;
    int end;

    // acquire block of tasks
    pthread_mutex_lock(&lock);
    c = next;
    next += 10;
    if (next <= len) {
	end = next;
    } else {
	end = len;
    }
    pthread_mutex_unlock(&lock);	

    // perform block of tasks
    while (c < end) {
	tasks[c] = 0;  // mark task c as started
	tasks[c] = 1;  // mark task c as finished
	assert(tasks[c] == 1);
	c++;
    }
}

void main() {
    pthread_t t;
    len = __VERIFIER_nondet_int();
    next = 0;
    assume(len > 0);
    pthread_mutex_init(&lock, NULL);
    tasks = malloc(len * sizeof(int));
    if (tasks > 0) {
	while(rand()){
	    pthread_create(&t, NULL, thread, NULL);
	}
    }
}

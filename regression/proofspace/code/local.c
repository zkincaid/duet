#include <pthread.h>

int g;

void* thread(void *arg) {
    int x;
    x = g;
    g = 2*x;
    return NULL;
}

void main() {
    pthread_t t;
    g = 0;
    while(rand()){
	pthread_create(&t, NULL, thread, NULL);
    }
    assert(g >= 0);
}

#include <pthread.h>

int count;

void* thread(void *arg) {
    count = count + 1;
    return NULL;
}

void main() {
    pthread_t t;
    count = 0;

    pthread_create(&t, NULL, thread, NULL);
    pthread_create(&t, NULL, thread, NULL);

    assert(count <= 2);
}

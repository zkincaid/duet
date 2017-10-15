#include <pthread.h>

int count;

void* thread(void *arg) {
    count++;
    return NULL;
}

void main() {
    count = 0;

    for (int i = 0; i < 75; ++i){
      pthread_t t;
      pthread_create(&t, NULL, thread, NULL);
    }

    assert(count <= 75);
}

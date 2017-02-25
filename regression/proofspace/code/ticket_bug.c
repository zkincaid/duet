#include <pthread.h>

int in_critical;
int s;
int t;

pthread_mutex_t lock;

void* thread(void *arg) {
    int m;
    m = t++;
    assume (s == m);
    in_critical = 1;
    assert(in_critical == 1);
    in_critical = 0;
    s++;
    return NULL;
}


void main() {
    pthread_t th;

    s = t = 0;
    pthread_create(&th, NULL, thread, NULL);
    pthread_create(&th, NULL, thread, NULL);
}

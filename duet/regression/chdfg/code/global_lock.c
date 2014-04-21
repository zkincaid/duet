#include <pthread.h>
pthread_mutex_t lock;
int x;

void t1 () {
    pthread_mutex_lock(&lock);
    assert(x == 0); // fail
    x = 1;
    assert(x == 1); // pass
    pthread_mutex_unlock(&lock);
}

void t2 () {
    pthread_mutex_lock(&lock);
    x = 2;
    pthread_mutex_unlock(&lock);
}

void main () {
    pthread_t th1, th2;
    pthread_create(&th1, NULL, t1, NULL);
    pthread_create(&th2, NULL, t2, NULL);
}

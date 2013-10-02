#include <pthread.h>

pthread_mutex_t lock;
int x;
int y;
void thread () {
    int *p,*q;
    p = &x;
    q = &y;
    *p = 1;
    x = 0;
    if (rand()) {
	assert(x == 0); // fail
    }
    assert(x <= 1); // pass

    pthread_mutex_lock(&lock);
    *q = 1;
    y = 0;
    assert(y == 0); // pass
    pthread_mutex_unlock(&lock);
}

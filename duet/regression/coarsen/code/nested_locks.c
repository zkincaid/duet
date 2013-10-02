/* Check that the coarsen algorithm is operating correctly on nested locks.
 * Expected output:
 *   1 error
 *   1 safe
 */

#include <pthread.h>

void assert(int);
pthread_mutex_t lock1;
pthread_mutex_t lock2;
int x;
int y;

void init () {
    x = 0;
    y = 0;
}
void thread0 () {
    pthread_mutex_lock(&lock1);
    pthread_mutex_lock(&lock2);
    pthread_mutex_unlock(&lock2);
    assert(x == 0); /* (A) */
    assert(y == 0); /* (B) */
    pthread_mutex_unlock(&lock1);
}

void thread1 () {
    pthread_mutex_lock(&lock2);
    y = 1; /* should reach (B) */
    y = 0;
    pthread_mutex_lock(&lock1);
    pthread_mutex_unlock(&lock1);
    x = 1; /* should not reach (A) */
    x = 0;
    pthread_mutex_unlock(&lock2);
}

/* Producer/consumer example with batch production
 * Additional flags: -parameterized
 * Expected output:
 *   0 errors
 *   1 safe
 */
#include <stdlib.h>
#include <pthread.h>

#define SIZE 50
#define ERROR -1
pthread_mutex_t lock1;
pthread_mutex_t lock2;
int counter;
void assert(int);

void init() {
    counter = 0;
}

int producer(int batch) {
    pthread_mutex_lock(&lock2);
    pthread_mutex_lock(&lock1);
    if (counter > 0) {
	counter++;
	pthread_mutex_unlock(&lock1);
	pthread_mutex_unlock(&lock2);
	return 1;
    } else {
	pthread_mutex_unlock(&lock1);
	counter = 0;
	while (batch > 0) {
	    counter++;
	    batch--;
	}
	batch = counter;
	pthread_mutex_unlock(&lock2);
	return batch;
    }
}

void consumer() {
    while (1) {
	pthread_mutex_lock(&lock1);
	if (counter > 0) { break; }
	pthread_mutex_unlock(&lock1);
    }
    counter--;
    assert(counter >= 0);
    pthread_mutex_unlock(&lock1);
}

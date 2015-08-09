#include <pthread.h>

int in_critical;
int s = 0;
int t = 0;
void* thread(void *arg) {
    int m;
    m = t++;
    assume (s == m)
    in_critical = 1;
    assert(in_critical == 1);
    in_critical = 0;
    s++;
    return NULL;
}


void main() {
    pthread_t t;

    s = t = 0;
    int num = 2;
    int i;
    for (i = 0; i < num; i++) {
	pthread_create(&t, NULL, thread, NULL);
    }
}

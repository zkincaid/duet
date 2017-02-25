#include <pthread.h>

int in_critical;
int e1;
int e2;
int n1;
int n2;

void* thread1(void *arg) {
    int tmp;
    e1 = 1;
    tmp = n2;
    n1 = tmp + 1;
    e1 = 0;
    assume (e2 != 0);
    assume (n2 == 0 || n2 >= n1);
    in_critical = 1;
    assert(in_critical == 1);
    n1 = 0;
    return NULL;
}

void* thread2(void *arg) {
    int tmp;
    e2 = 1;
    tmp = n1;
    n2 = tmp + 1;
    e2 = 0;
    assume (e1 != 0);
    assume (n1 == 0 || n1 > n2);
    in_critical = 2;
    assert(in_critical == 2);
    n2 = 0;
    return NULL;
}

void main() {
    pthread_t t1, t2;
    e1 = e2 = 0;
    n1 = n2 = 0;

    pthread_create(&t1, NULL, thread1, NULL);
    pthread_create(&t2, NULL, thread2, NULL);
}

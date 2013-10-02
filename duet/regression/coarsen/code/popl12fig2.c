#include<pthread.h>

int c;

void *func1() {
    int incr;
    incr = 1;
    c = c + incr;
    return 0;
}

void *func2() {
    int incr;
    incr = -1;
    assert(c>=0); // pass
    assert(c<=0); // fail
    return 0;
}


int main()
{
    pthread_t t1, t2;
    void *status;
    c = 0;

    pthread_create(&t1, NULL, func1, NULL );
    pthread_create(&t2, NULL, func2, NULL);

    pthread_join(t1, &status);
    pthread_join(t2, &status);

    pthread_exit(NULL);
    return 0;
}

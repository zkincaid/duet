/* Test *direct* procedure calls */

#include <stdlib.h>
#include <pthread.h>
int global;

int *global_ptr;

void foo (int **a, int *b) {
    *a = b;
}
void* bar (void *c) {
    *((int**) c) = &global;
    global_ptr = &global;
    return (void*) &global;
}
int *baz () {
    return malloc(sizeof(int));
}

void main () {
    int x, y;
    int *p, *q, *r;
    pthread_t thread;
    p = &x;
    q = &y;
    foo(&q, p);
    pthread_create(&thread, NULL, bar, (void*) &p);
    foo(&r, q);
    r = baz();
}
/*
  global_ptr -> {&global}
  a -> {&q, &r}
  b -> {&global, &x, &y}
  c -> {&p}
  p -> {&global, &x}
  q -> {&global, &x, &y}
  r -> {alloc#16, &global, &x, &y}
*/

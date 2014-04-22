/* Test *direct* procedure calls */

#include <stdlib.h>
#include <pthread.h>
int global;

int *global_ptr;
int *m;

void foo (int **a, int *b) {
    if(rand()) {
	assert(a != b); // pass
    } else {
	assert(*a != &global); // fail
    }
    *a = b;
}
void* bar (void *c) {
    *((int**) c) = &global;
    global_ptr = &global;
    return (void*) &global;
}
int *baz () {
    m = malloc(sizeof(int));
    return m;
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
    switch(rand()){
    case 0: assert(p != &global); // fail
    case 1: assert(p != &x); // fail
    case 2: assert(p != &y); // pass

    case 3: assert(q != &global); // fail
    case 4: assert(q != &x); // fail
    case 5: assert(q != &y); // fail

    case 6: assert(r != &global); // fail
    case 7: assert(r != &x); // fail
    case 8: assert(r != &y); // fail
    case 8: assert(r != m); // fail

    default: assert(global_ptr != &global); // fail
    }
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

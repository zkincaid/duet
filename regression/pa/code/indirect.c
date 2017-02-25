/* Indirect calls */

void* bar(int (*f)(void*));
void* baz(int (*e)(void*));
void* foo(int (*g)(void*)) {
    switch(rand()){
    case 0: assert(g != &foo); // fail
    case 1: assert(g != &bar); // fail
    default: assert(g != &baz); // pass
    }
    return (*g)(bar);
}

void* bar(int (*h)(void*)) {
    switch(rand()){
    case 0: assert(h != &foo); // pass
    case 1: assert(h != &bar); // fail
    default: assert(h != &baz); // fail
    }
    return (*h)(baz);
}

void* baz(int (*e)(void*)) {
    switch(rand()){
    case 0: assert(e != &foo); // pass
    case 1: assert(e != &bar); // pass
    default: assert(e != &baz); // fail
    }
    return (*e)(baz);
}

int main () {
    int (*f)(void*);
    int x;
    f = foo;
    (*f)(foo);

    switch(rand()){
    case 0: assert(f != &foo); // fail
    case 1: assert(f != &bar); // pass
    default: assert(f != &baz); // pass
    }

    return 0;
}

/*
  e -> {&baz}
  f -> {&foo}
  g -> {&foo, &bar}
  h -> {&bar, &baz}
*/

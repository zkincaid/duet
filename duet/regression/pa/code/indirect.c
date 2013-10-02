/* Indirect calls */

void* bar(int (*f)(void*));
void* baz(int (*e)(void*));
void* foo(int (*g)(void*)) {
    return (*g)(bar);
}

void* bar(int (*h)(void*)) {
    return (*h)(baz);
}

void* baz(int (*e)(void*)) {
    return (*e)(baz);
}

int main () {
    int (*f)(void*);
    int x;
    f = foo;
    (*f)(foo);
    return 0;
}

/*
  e -> {&baz}
  f -> {&foo}
  g -> {&foo, &bar}
  h -> {&bar, &baz}
*/

struct foo_t {
    int int_field;
    int array_field[32];
};
int foo (int x) {
    return x;
}

int main () {
    int *x;
    int array[10];
    int y;
    int *z;
    struct foo_t some_foo;

    /* All of these should be considered allocations */
    x = z = (int*) "string constant";
    x = array;
    x = (int*) foo;
    x = &y;
    x = some_foo.array_field;

    switch(rand()){
    case 0: assert(x != &array); // fail
    case 1: assert(x != &foo); // fail
    case 2: assert(x != &y); // fail
    case 2: assert(x != z); // fail
    default: assert(x != &some_foo.array_field); // fail
    }
    return 0;
}

/*
  x -> {"string constant",&array,&foo,&y,&some_foo.array_field}
 */

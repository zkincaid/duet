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
    struct foo_t some_foo;

    /* All of these should be considered allocations */
    x = (int*) "string constant";
    x = array;
    x = (int*) foo;
    x = &y;
    x = some_foo.array_field;

    return 0;
}

/*
  x -> {"string constant",&array,&foo,&y,&some_foo.array_field}
 */

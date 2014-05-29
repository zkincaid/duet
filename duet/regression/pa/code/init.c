int a;
int b;
int c;
int d;
int *p;

void foo(int **q) {
    *q = &a;
}

int (*f)(int**) = foo;

struct s {
    int *f1;
    int *f2;
};

struct s some_struct = { .f1 = &a, .f2 = &b };

struct s some_array[3] = {
    { .f1 = &a, .f2 = &b },
    { .f1 = &c, .f2 = &d }
};

void main() {
    f(&p);
    switch(rand()) {
    case 0: assert(p != &a); // fail
    case 1: assert(some_struct.f1 != &a); // fail
    case 2: assert(some_struct.f2 != &b); // fail
    case 3: assert(some_array[0].f1 != &a); // fail
    case 4: assert(some_array[0].f2 != &b); // fail
    case 5: assert(some_array[1].f1 != &c); // fail
    default: assert(some_array[1].f2 != &d); // fail
    }
}

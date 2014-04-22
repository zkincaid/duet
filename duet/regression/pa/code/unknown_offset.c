struct foo_t {
    int *p;
    int *q;
};

int main () {
    struct foo_t x, y;
    int *p, *q;
    int a, b;
    int i = 0;
    *(&x.p + i) = (int*) &y; /* conservatively assume that this writes to x.p
				and x.q */
    y.p = &a;
    y.q = &b;
    q = *(&y.p + i); /* conservatively assume that this reads from y.p and
			y.q */
    p = x.q;

    switch(rand()) {
    case 0: assert(p != &y); // fail

    case 1: assert(q != &a); // fail
    case 2: assert(q != &b); // fail

    case 3: assert(x.p != &y); // fail
    case 4: assert(x.q != &y); // fail

    case 5: assert(y.p != &a); // fail
    default: assert(y.q != &b); // fail
    }
    return 0;
}

/*
  p -> {&y}
  q -> {&a,&b}
  x.p -> {&y}
  x.q -> {&y}
  y.p -> {&a}
  y.q -> {&b}
*/

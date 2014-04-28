/* Complicated right hand sides */

int main () {
    int *p, *q, *r, *s;
    int a, b, c;
    p = &a + ((int) &b); /* Unknown offset */
    a = (int) &b;
    b = (int) &c;
    q = (int*) *(&a + a); /* 0 offset */
    r = (int*) *(&a + a) + 1; /* 1 offset */
    s = r - 1; /* 0 offset, but the analysis can't figure that out */

    switch(rand()) {
    case 0: assert(p != &a); // fail
    case 1: assert(p != &a + 42); // fail

    case 2: assert(r != &b + 1); // fail
    case 3: assert(r != &b); // pass
    case 4: assert(r != &b + 2); // pass
    case 5: assert(r != &c + 1); // fail
    case 6: assert(r != &c); // pass
    case 7: assert(r != &c + 2); // pass
    }
    return 0;
}

/*
  p -> {&a.unknown, &b.unknown}
  q -> {&b, &c}
  r -> {&b.1, &c.1}
  s -> {&b.unknown, &c.unknown}
  a -> {&b}
  b -> {&c}
*/

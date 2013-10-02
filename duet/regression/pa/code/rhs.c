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

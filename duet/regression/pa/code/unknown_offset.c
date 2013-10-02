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

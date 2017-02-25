void main() {
    int *p = 100;
    int *q = 200;
    assert(p + 5 == 100 + 5*sizeof(int));
    assert(p - 10 == 100 - 10*sizeof(int));
    assert(p - q == -100/sizeof(int));
    assert(q - p == 100/sizeof(int));
}

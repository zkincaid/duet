void main() {
    int *p = 100;
    int *q = 200;
    __VERIFIER_assert(p + 5 == 100 + 5*sizeof(int));
    __VERIFIER_assert(p - 10 == 100 - 10*sizeof(int));
    __VERIFIER_assert(p - q == -100/sizeof(int));
    __VERIFIER_assert(q - p == 100/sizeof(int));
}

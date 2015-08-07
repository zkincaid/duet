int add(int x, int y) {
    //    assert(x == 0); // succeed
    //    assert(y == 1); // succeed
    return x + y;
}
int sub(int x, int y) {
    //assert(x == 1); // fail
    return x - y;
}
void main() {
    int i = 0;
    i = add(i, 1);
    //i = sub(i, 1);
    //i = sub(i, 0);
    assert(i == 2); // succeed
}

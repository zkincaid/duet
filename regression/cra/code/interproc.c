int add(int x, int y) {
    assert(x == 0); // succeed
    assert(y == 1); // succeed
    return x + y;
}
int sub(int x, int y) {
    return x - y;
}
void main() {
    int i = 0;
    i = add(i, 1);
    i = sub(i, 1);
    assert(i == 0); // succeed
}

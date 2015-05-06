int add(int x, int y) {
    assert(x == 0);
    assert(y == 1);
    return x + y;
}
void main() {
    int i = 0;
    int n = rand();
    assume(n > 0);
    //    while (i < n) {
    i = add(i, 1);
	//    }
    assert(i == 1);
}

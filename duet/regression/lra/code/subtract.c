void main () {
    int x, y, result, tmp;
    x = rand();
    y = rand();
    assume(y >= 0);
    tmp = y;
    result = x;
    while (tmp > 0) {
	tmp = tmp - 1;
	result = result - 1;
    }
    assert(result == x - y);
}

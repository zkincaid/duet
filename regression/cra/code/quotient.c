
int x, y, q, r, tmp;
void subtract() {
    int tmp;
    tmp = y;
    while (tmp > 0) {
	tmp = tmp - 1;
	r = r - 1;
    }
}

void main () {
    x = rand();
    y = rand();
    q = 0;
    r = x;
    while (r > y) {

	// r = r - y;
	assume(y >= 0);

	subtract();
	//r = r - y;

	q = q + 1;
    }
    assert(x == q*y + r);
}

void main() { 
    int i, n = rand(),q = rand(), r;
    r = n;
    assume(n > q);
    assume(q >= 1);
    i = 0;
    while(r > q) {
	r = r - q;
	i = i + 1;
    }
    assert(i * q + r == n);
}

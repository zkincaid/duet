void main() { 
    int i, n,m,r;//n = rand(), m = rand(), r;
    //    tmpl("(le(i,n,m,r),le(i,n,m,r))");
    assume(n > 0);
    i = 0;
    r = 0;
    m = m;
    n = n;
    while(i < n) {
	r = r + m;
	i++;
    }
    assert(i == n);
    assert(r == n * m);
}

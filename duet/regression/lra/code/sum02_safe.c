void main() { 
    unsigned int i, n, sn;
    sn = 0;
    for(i = 0; i <= n; i++) {
	sn = sn + i;
    }
    assert(sn==(n*(n+1))/2 || sn == 0);
}

int n;
int m;
void mult(int r, int i) {
    if (i < n) {
	mult(r + m, i + 1);
    } else {
	assert(i == n);
	assert(r == n * m);
    }
}
void main() { 
    assume(n > 0);
    mult(0, 0);
}

void *malloc(int);
void main() {
    int *a, i;
    int n;
    n = 10;
    a = malloc(n*sizeof(int));
    for (i = 0; i < n; i++) {
	a[i] = 0;
    }
    while(n > 0) {
	*a = 1;
	n--;
	a++;
    }
}

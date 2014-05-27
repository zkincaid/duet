void main() {
    int *p = malloc(sizeof(int));
    int i;
    *p = 0;
    for(i = 0; i < 10; i++) {
	assert(*p == 0);
    }
}

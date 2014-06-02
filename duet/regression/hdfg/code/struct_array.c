struct point {
    int x;
    int y;
};
struct point a[10];
void main() {
    int i;
    struct point *b = malloc(sizeof(struct point)*10);
    for(i = 0; i < 10; i++) {
	a[i].x = 0;
	a[i].y = 0;
	b[i].x = 0;
	b[i].y = 0;
    }
}

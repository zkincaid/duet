int f(int x, int* y) {
    if (x > 0) {
        *y = 1;
        return 40;
    } else {
        return 3;
    }
}
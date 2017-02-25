#define a 0.001
void main () {
    float x, y, result, tmp;
    assume(y >= 0);
    tmp = y;
    result = x;
    while (tmp > 0) {
	tmp = tmp - a;
	result = result - a;
    }
    if (rand()) {
	assert(x - y - result < a);  // succeed
	assert(x - y - result >= 0); // succeed
    } else {
	assert(result == x - y);     // fail
    }
}

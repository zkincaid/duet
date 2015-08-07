int loop(int x) {
    if (x < 10) {
	return loop(x + 1);
    } else {
	return x;
    }
}

void main() {
    int x;
    x = loop(0);
    switch (rand()) {
    case 0:
	assert(x <= 1); // unsafe
	break;
    case 1:
	assert(x >= 0); // safe
	break;
    case 2:
	assert(x <= 10); // safe
	break;
    default:
	assert(x == 10); // safe
    }
}

int x;
void loop() {
    if (x < 10) {
	x = x + 1;
	loop();
    } else {
	switch (rand()) {
	case 0:
	    __VERIFIER_assert(x <= 1); // unsafe
	    break;
	case 1:
	    __VERIFIER_assert(x >= 0); // safe
	    break;
	case 2:
	    __VERIFIER_assert(x <= 10); // safe
	    break;
	default:
	    __VERIFIER_assert(x == 10); // safe
	}
    }
}

void main() {
    x = 0;
    loop();
}

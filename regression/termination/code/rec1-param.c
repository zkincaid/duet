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
    switch (__VERIFIER_nondet_int()) {
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

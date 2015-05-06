void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
_Bool __VERIFIER_nondet_bool();

void f(int d) {
    int x, y, k, z = 1;
    while (z < k) { z = 2 * z; }
    assert(z>=1);
    while (x > 0 && y > 0) {
	int c = rand();
	if (c) {
	    x = x - d;
	    y = rand();
	    z = z - 1;
	} else {
	    y = y - d;
	}
	y = y;
    }
}

void main() {
    int c = rand();
    if (c) {
	f(1);
    } else {
	f(2);
    }
}

int main () {
    int x;
    x = 0;

    if (x < 10) {
	x++;
	goto L0;
    } else if (x > 0) {
	goto L1;
    } else {
	goto L2;
    }
 L0:
 L1:
    x--;
 L2:
    switch (x) {
    case 0: x = 0;
    case 1: x = 1; break;
    case 2: x = 2; break;
    default: switch (x) {
	case 3: x = 3; break;
	case 4: x = 4;
	}
    }

    return 0;
}

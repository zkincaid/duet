/* Implementation of Dekker's mutual exclusion algorithm.
 * Expected ouput:
 *  1 error (line 38)
 *  1 safe assertion (line 59)
 */

int flag0;
int flag1;
int turn;
int x;
int y;
void assume(int);
void assert(int);
void init() {
    flag0 = 0;
    flag1 = 0;
    turn = 0;
    x = 0;
    y = 0;
}

void thread0() {
    flag0 = 1;
    while (flag1 == 1) {
	if (turn != 0) {
	    flag0 = 0;
	    assume(turn == 0);
	    flag0 = 1;
	}
    }
    // assume flag1 == 0

    // enter critical section
    // invariants: flag1=1
    x = 1;
    x = 0;
    assert(y == 0); /* may fail */
    // exit critical section
    turn = 1;
    flag0 = 0;
}

void thread1() {
    flag1 = 1;
    while (flag0 == 1) {
	if (turn != 1) {
	    flag1 = 0;
	    assume(turn == 1);
	    flag1 = 1;
	}
    }
    // assume flag0 == 0

    // enter critical section
    // invariants: flag1=1
    y = 0;
    y = 1;
    assert(x == 0); /* safe */
    // exit critical section
    turn = 0;
    flag1 = 0;
}


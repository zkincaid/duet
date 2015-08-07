/* Simple rendez-vous check
 * Expected output:
 *   0 error
 *   1 safe
 */

void assert(int);
void assume(int);
int flag;
int x;

void init () {
    flag = 0;
    x = 0;
}

void thread0 () {
    x = 1; /* shouldn't reach the assertion */
    x = 0;
    flag = 1; /* send */
}

void thread1 () {
    assume(flag); /* receive */ 
    assert(!x);
}

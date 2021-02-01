/* Adding a precondition to a loop that Ultimate automizer can solve
  can make the tool timeout.
 */
extern int __VERIFIER_nondet_int(void);

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int z = __VERIFIER_nondet_int();
    int a = __VERIFIER_nondet_int();
    int b = __VERIFIER_nondet_int();
    if (y > 9999) return 0;
    if (z > 999999) { // without this condition UAutomizer could prove it quickly
        while (z >= 0 && __VERIFIER_nondet_int()) {
            z = z - 1;
        }
        if (a == b) {
            while (x >= 0 && y >= 0) {
                y = y - z;
                while (z > 0) {
                    z = z - 1;
                    y = y + 2 * z - x;
                }
                x = x + a - b - 1;
            } 
        }

    }
    
    return 0;
}
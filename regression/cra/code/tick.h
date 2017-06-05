
int __cost; // current (memory) usage

#define init_tick(k) {__cost = (k);}
// You could add a semicolon here, and __VERIFIER_assume(hwm >= cost)


#define tick(k) { \
                 __VERIFIER_assume(__cost >= 0); \
                 __VERIFIER_assume(__cost + k >= 0); \
                 __cost = __cost + (k); \
                 }


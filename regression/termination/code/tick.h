
int __cost; // current (memory) usage

#define init_tick(k) {__cost = (k);}
// You could add a semicolon here, and __VERIFIER_assume(hwm >= cost)


#define tick(k) __cost = __cost + (k)

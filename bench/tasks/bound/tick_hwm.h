int __cost; // current (memory) usage

int __hwm;  // high water mark: the largest amount of memory that we've
          //   needed at any point during this execution 

#define init_tick(k) {__cost = (k); __hwm = (k);}
// You could add a semicolon here, and __VERIFIER_assume(hwm >= cost)

#define tick(k) { \
                 __VERIFIER_assume(__cost + (k) >= 0); \
                 __VERIFIER_assume(__hwm >= __cost); \
                 __VERIFIER_assume(__cost >= 0); \
                 __VERIFIER_assume(__hwm >= 0); \
                 __cost = __cost + (k); \
                 __hwm = (__hwm >= __cost) ? __hwm : __cost; \
                 }


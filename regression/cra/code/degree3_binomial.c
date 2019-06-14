#include "tick.h"

void work(int n) {
    for(int i = 0; i < n; i++) {
        for(int j = 0; j < i; j++) {
            for(int k = 0; k < j; k++) {
                tick(1);
            }
        }
    }
}

int main(int argc, char ** argv) {
    init_tick(0);
    int P = (argv[1] != 0) ? atoi(argv[1]) : 0;
    work(P);
    int maxP0 = (P < 0) ? 0 : P;
    __VERIFIER_assert(6 * __cost == (maxP0 - 2) * (maxP0 - 1) * maxP0);
    return 0;
}

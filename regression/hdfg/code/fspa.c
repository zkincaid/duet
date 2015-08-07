#include <stdlib.h>

int main() {
    int *p,*q,*r;
    int havoc;
    p = malloc(sizeof(int)); /* alloc1 */
    r = malloc(sizeof(int)); /* alloc2 */
    if (havoc) {
	q = (int*) &r; /* &r */
    } else {
	q = malloc(sizeof(int)); /* alloc3 */
    }
    *q = (int) &havoc; /* &havoc */
    q = p - q; /* alloc1.Top, &r.Top, alloc3.Top */
    while (havoc) {
	q = q - r; /* alloc1.Top, &r.Top, alloc3.Top, &havoc.Top */
    }
    return 0;
}

#include "assert.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Adapted from "Automated Error Diagnosis Using Abductive Inference" by Dillig et al.
 */

int main() {
   int n = unknown2();
   int flag = unknown3();
   assume(n>=0);
   assume(n < LARGE_INT);
   int k = 1;
   if(flag) {
	k = unknown1();
	assume(k>=0);
   }
   int i = 0, j = 0;
   while(i <= n) {
     i++;
     j+=i;
   }
   int z = k + i + j;
   static_assert(z > 2*n);
}


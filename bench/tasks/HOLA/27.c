#include "assert.h"

/*
 * "nested2.c" from InvGen benchmark suite
 */

int unknown1();
int unknown2();
void main() {
  int i,k,n,l;

  n = unknown1();
  l = unknown2();
  assume(l>0);

  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {

    }
    for (i=l;i<n;i++) {
      static_assert(1<=k);
    }
  }

}

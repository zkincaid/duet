//#include "assert.h"

/*
 * "nested4.c" from InvGen benchmark suite
 */


extern void __VERIFIER_assume (int);
extern void __VERIFIER_error (void);
void assert (int v) { if (!v) __VERIFIER_error (); }

#define assume __VERIFIER_assume
#define static_assert assert

int unknown1();
int unknown2();
void main() {
  int i,k,n,l;

  l = unknown1();
  l = unknown2();
  __VERIFIER_assume(l>0);

  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {
    }
    for (i=l;i<n;i++) {
	static_assert(1<=i);
    }
  }
}

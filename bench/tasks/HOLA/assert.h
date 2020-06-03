extern void __VERIFIER_error() __attribute__((noreturn));
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int ();

#define static_assert __VERIFIER_assert

// uncomment for seahorn
/*
void static_assert(int cond) {
    if (!cond) {
	__VERIFIER_error ();
    }
    }*/

#define assume __VERIFIER_assume
#define LARGE_INT 100000

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
void assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}


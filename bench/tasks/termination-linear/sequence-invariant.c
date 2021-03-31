/* Sequential composition of two loops, such that an invariant for the
   first is required to prove termination of the second */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = 0;
  int z = __VERIFIER_nondet_int();
  
  while(y < z) {
    y += 2;
  }

  if (z % 2 == 0) { return 0; }

  // Precondition: y > z

  while(x > 0) {
    x = x - y + z;
  }
  return 0;
}

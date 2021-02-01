/* Disjunctive guards with different termination arguments */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  while (x % 17 != 0 || y >= 0) {
    x = x + 3;
    y = y - z;
    z = z + 1;
  }
  return 0;
}

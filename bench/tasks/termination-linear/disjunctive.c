/* A linear loop with a disjunctive guard */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int step = __VERIFIER_nondet_int();
  if (step <= 0) { return 0; }
  while(x > 0 || y > 0) {
    x = x - step;
    y = y - step;
  }
  return 0;
}

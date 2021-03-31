// Source: Amir M. Ben-Amram, Samir Genaim, "On Multiphase-Linear
// Ranking Functions", CAV 2017.


extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x1 = __VERIFIER_nondet_int();
  int x2 = __VERIFIER_nondet_int();
  int x3 = __VERIFIER_nondet_int();

  // avoid overflow
  if (x1 > 1000 || x2 > 1000 || x3 > 1000) return 0;
  if (x1 < -1000 || x2 < -1000 || x3 < -1000) return 0;

  while (x2 - x1 <= 0 && x1 + x2 >= 1 && x3 >= 0) {
    x2 = x2 - 2 * x1 + 1;
    x3 = x3 + 10 * x2 + 9;
  }

  return 0;
}

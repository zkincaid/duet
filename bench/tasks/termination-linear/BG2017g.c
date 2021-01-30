// Source: Amir M. Ben-Amram, Samir Genaim, "On Multiphase-Linear
// Ranking Functions", CAV 2017.


extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();

  while (x >= 0) {
    x = x + y;
    y = y - 1;
  }

  return 0;
}

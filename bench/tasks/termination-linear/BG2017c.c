// Source: Amir M. Ben-Amram, Samir Genaim, "On Multiphase-Linear
// Ranking Functions", CAV 2017.


extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  while (x >= 0 && y <= 10 && z >= 0 && z <= 1) {
    x = x + y + z - 10;
    y = y + z;
    z = 1 - z;
  }
}

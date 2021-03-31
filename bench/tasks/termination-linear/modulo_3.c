/* Reasoning about the periodic behavior of modulos w.r.t. linear mappings */
extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  if (x % 7 == 1 || x % 7 == 3) {
    while (x % 7 != 0) {
      x = 2 * x + 1;
    }
  }
  return 0;
}

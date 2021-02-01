/* Basic reasoning of modulo operations */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  while (x > 0) {
    if (x % 2 == 1) break;
    x = x / 2;
  }
  return 0;
}

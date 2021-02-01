/* Basic reasoning of modulo operations */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  while (x % 37 != 0) {
    x = x + 5;
  }
  return 0;
}

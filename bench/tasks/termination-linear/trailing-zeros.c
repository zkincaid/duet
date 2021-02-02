/* Basic reasoning of integer division operations */

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  int c = 0;
  while (x % 2 == 0) {
    x = x / 2;
    c = c + 1;
  }
  return 0;
}

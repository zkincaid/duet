/* Reasoning about the periodic behavior of modulos w.r.t. linear mappings */
extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  while (x % 128 == 1) {
    x = (x - 1) / 128;
    x = x * 12;    
  }
  return 0;
}

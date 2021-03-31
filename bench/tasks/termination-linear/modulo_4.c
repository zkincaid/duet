/* Reasoning about the periodic behavior of modulos w.r.t. linear mappings */
extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  if (x <= 0 || x > 999999) return 0;
  while (x % 256 == 1) {
    x = (x - 1) / 256;
    x = x * 384;    
  }
  return 0;
}

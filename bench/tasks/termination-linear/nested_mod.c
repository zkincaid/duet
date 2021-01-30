// Find smallest number that is greater than x and is equal to 7 mod 10

extern int __VERIFIER_nondet_int(void);

int main(int argc, char* argv[]) {
  int x = __VERIFIER_nondet_int();
  int r;
  __VERIFIER_assume(x >= 0);
  do {
    // calculate r = x mod 10
    r = x;
    while (r >= 10) {
      r = r - 10;
    }
    x++;
  } while (r != 7);
  return x;
}

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
#define a 0.1
extern int __VERIFIER_nondet_int();
void main() {
    int i, n;
    float sn=0;
    for(i=1; i<=n; i++) {
	sn = sn + a;
    }
    assert(sn==n*a || sn == 0);
}

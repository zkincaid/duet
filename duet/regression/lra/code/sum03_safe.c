void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
#define a (2)
unsigned int __VERIFIER_nondet_uint();

int main() { 
  int sn=0;
  unsigned int x=0;

  while(1){
    sn = sn + a;
    x++;
    assert(sn==x*a || sn == 0);
  }
}


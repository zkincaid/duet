extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x1;
  signed int x2;
  x1 = nondet_signed_int();
  x2 = nondet_signed_int();
  for( ; !(x1 >= 11); x1 = x1 + 1)
  {
    x2 = 1000;
    for( ; x2 >= 2; x2 = x2 - 1)
      while(!(!(x2 - 1 < (-0x7fffffff - 1) || 0x7fffffff < x2 - 1)));
    while(!(!(x1 + 1 < (-0x7fffffff - 1) || 0x7fffffff < x1 + 1)));
  }
  return 0;
}

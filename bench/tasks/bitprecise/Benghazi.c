extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int x;
  signed int d1;
  signed int d2;
  signed int d1old;
  d1 = 73;
  d2 = 74;
  x = nondet_signed_int();
  for( ; x >= 0; d2 = d1old + 1)
  {
    while(!(!(x - d1 < (-0x7fffffff - 1) || 0x7fffffff < x - d1)));
    x = x - d1;
    d1old = d1;
    while(!(!(d2 + 1 < (-0x7fffffff - 1) || 0x7fffffff < d2 + 1)));
    d1 = d2 + 1;
    while(!(!(d1old + 1 < (-0x7fffffff - 1) || 0x7fffffff < d1old + 1)));
  }
  return 0;
}

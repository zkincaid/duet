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
  signed int xtmp;
  signed int res;
  signed int restmp;
  x = nondet_signed_int();
  res = 0;
  for( ; x >= 2; res = res + 1)
  {
    xtmp = x;
    restmp = 0;
    for( ; xtmp >= 2; restmp = restmp + 1)
    {
      while(!(!(xtmp - 2 < (-0x7fffffff - 1) || 0x7fffffff < xtmp - 2)));
      xtmp = xtmp - 2;
      while(!(!(restmp + 1 < (-0x7fffffff - 1) || 0x7fffffff < restmp + 1)));
    }
    x = xtmp;
    while(!(!(res + 1 < (-0x7fffffff - 1) || 0x7fffffff < res + 1)));
  }
  return 0;
}

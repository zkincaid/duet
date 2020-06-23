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
  signed int a;
  signed int b;
  x = nondet_signed_int();
  a = nondet_signed_int();
  b = nondet_signed_int();
  if(!(x >= -268435455) || x >= 268435456)
    return 0;
  else
    if(!(a >= -268435455) || a >= 268435456)
      return 0;
    else
      if(!(b >= -268435455) || b >= 268435456)
        return 0;
      else
      {
        if(a == b)
          for( ; x >= 0; x = ((x + a) - b) - 1)
          {
            while(!(!(x + a < (-0x7fffffff - 1) || 0x7fffffff < x + a)));
            while(!(!(a + x - b < (-0x7fffffff - 1) || 0x7fffffff < a + x - b)));
            while(!(!(a + x + -b - 1 < (-0x7fffffff - 1) || 0x7fffffff < a + x + -b - 1)));
          }
        return 0;
      }
}

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
  signed int y;
  signed int m;
  y = 0;
  m = nondet_signed_int();
  x = m;
  signed int return_value___VERIFIER_nondet_int;
  while(x >= 0 && y >= 0)
  {
    signed int return_value___VERIFIER_nondet_int$0=nondet_signed_int();
    if(!(return_value___VERIFIER_nondet_int$0 == 0))
    {
      for( ; m >= y; y = y + 1)
      {
        return_value___VERIFIER_nondet_int = nondet_signed_int();
        if(return_value___VERIFIER_nondet_int == 0)
          break;
        while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
      }
      while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
      x = x - 1;
    }
    while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
    y = y - 1;
  }
  return 0;
}

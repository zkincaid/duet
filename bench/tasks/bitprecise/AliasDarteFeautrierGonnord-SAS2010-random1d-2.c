extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int a;
  signed int x;
  signed int max=nondet_signed_int();
  if(max >= 1)
  {
    a = 0;
    x = 1;
    while(!(x >= max))
    {
      signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
      if(!(return_value___VERIFIER_nondet_int == 0))
      {
        while(!(!(a + 1 < (-0x7fffffff - 1) || 0x7fffffff < a + 1)));
        a = a + 1;
      }
      else
      {
        while(!(!(a - 1 < (-0x7fffffff - 1) || 0x7fffffff < a - 1)));
        a = a - 1;
      }
      while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
      x = x + 1;
    }
  }
  return 0;
}

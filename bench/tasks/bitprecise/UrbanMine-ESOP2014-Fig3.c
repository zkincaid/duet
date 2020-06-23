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
  x = nondet_signed_int();
  y = nondet_signed_int();
  while(y >= 1 && !(x == 0))
    if(x >= 1)
    {
      signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
      if(!(return_value___VERIFIER_nondet_int == 0))
      {
        while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
        x = x - 1;
        y = nondet_signed_int();
      }
      else
      {
        while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        y = y - 1;
      }
    }
    else
    {
      signed int return_value___VERIFIER_nondet_int$0=nondet_signed_int();
      if(!(return_value___VERIFIER_nondet_int$0 == 0))
      {
        while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
        x = x + 1;
      }
      else
      {
        while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        y = y - 1;
        x = nondet_signed_int();
      }
    }
  return 0;
}

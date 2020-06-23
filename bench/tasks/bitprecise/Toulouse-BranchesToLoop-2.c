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
  signed int z;
  y = nondet_signed_int();
  z = nondet_signed_int();
  if(!(y >= -268435455))
    return 0;
  else
    if(!(z >= -268435455))
      return 0;
    else
    {
      signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
      if(!(return_value___VERIFIER_nondet_int == 0))
        x = 1;
      else
        x = -1;
      for( ; !(y >= 100) && !(z >= 100); z = z - x)
      {
        while(!(!(y + x < (-0x7fffffff - 1) || 0x7fffffff < y + x)));
        y = y + x;
        while(!(!(z - x < (-0x7fffffff - 1) || 0x7fffffff < z - x)));
      }
      return 0;
    }
}

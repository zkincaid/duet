extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int i=nondet_signed_int();
  while(!(i >= 255))
  {
    signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
    if(!(return_value___VERIFIER_nondet_int == 0))
    {
      while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
      i = i + 1;
    }
    else
    {
      while(!(!(i + 2 < (-0x7fffffff - 1) || 0x7fffffff < i + 2)));
      i = i + 2;
    }
  }
  return 0;
}

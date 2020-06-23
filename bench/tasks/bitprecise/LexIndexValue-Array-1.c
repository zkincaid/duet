extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int a[1048l];
  signed int k=0;
  signed int i=0;
  for( ; !(i >= 1048); i = i + 1)
  {
    a[(signed long int)i] = nondet_signed_int();
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
  }
  while(!(k >= 1048))
  {
    if(!(a[(signed long int)k] >= 0))
      break;
    signed int return_value___VERIFIER_nondet_int=nondet_signed_int();
    if(!(return_value___VERIFIER_nondet_int == 0))
    {
      while(!(!(k + 1 < (-0x7fffffff - 1) || 0x7fffffff < k + 1)));
      k = k + 1;
    }
    else
    {
      while(!(!(a[(signed long int)k] - 1 < (-0x7fffffff - 1) || 0x7fffffff < a[(signed long int)k] - 1)));
      a[(signed long int)k] = a[(signed long int)k] - 1;
    }
  }
  return 0;
}

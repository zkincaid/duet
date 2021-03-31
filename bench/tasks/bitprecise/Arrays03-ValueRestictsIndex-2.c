extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int k=nondet_signed_int();
  signed int a[1048l];
  signed int i=0;
  for( ; !(i >= 1048); i = i + 1)
  {
    a[(signed long int)i] = nondet_signed_int();
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
  }
  if(k >= 0 && !(k >= 1048))
  {
    if(a[0l] == 23)
    {
      if(a[(signed long int)k] == 42)
      {
        signed int x=nondet_signed_int();
        for( ; x >= 0; x = x - k)
          while(!(!(x - k < (-0x7fffffff - 1) || 0x7fffffff < x - k)));
      }
    }
  }
  return 0;
}

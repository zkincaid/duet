extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int c;
  signed int i;
  signed int j;
  i = nondet_signed_int();
  j = nondet_signed_int();
  c = 0;
  for( ; i >= 0; i = i - 1)
  {
    j = 0;
    do
    {
      while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
      if(!(-1 + i >= j))
        break;
      while(!(!(j + 1 < (-0x7fffffff - 1) || 0x7fffffff < j + 1)));
      j = j + 1;
    }
    while((char)1);
    while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
  }
  return 0;
}

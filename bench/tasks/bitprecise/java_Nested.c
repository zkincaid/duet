extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int i;
  signed int j;
  signed int c=0;
  i = 0;
  for( ; !(i >= 10); i = i + 1)
  {
    j = 3;
    for( ; !(j >= 12); j = j + 2)
    {
      while(!(!(j - 1 < (-0x7fffffff - 1) || 0x7fffffff < j - 1)));
      j = j - 1;
      while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
      c = c + 1;
      while(!(!(j + 2 < (-0x7fffffff - 1) || 0x7fffffff < j + 2)));
    }
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
  }
  return 0;
}

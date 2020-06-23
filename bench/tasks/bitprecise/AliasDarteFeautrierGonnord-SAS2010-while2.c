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
  signed int N=nondet_signed_int();
  i = N;
  for( ; i >= 1; i = i - 1)
  {
    j = N;
    for( ; j >= 1; j = j - 1)
      while(!(!(j - 1 < (-0x7fffffff - 1) || 0x7fffffff < j - 1)));
    while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
  }
  return 0;
}

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
  signed int j=1;
  i = 10000;
  do
  {
    while(!(!(i - j < (-0x7fffffff - 1) || 0x7fffffff < i - j)));
    if(!(i + -j >= 1))
      break;
    while(!(!(j + 1 < (-0x7fffffff - 1) || 0x7fffffff < j + 1)));
    j = j + 1;
    while(!(!(i - 1 < (-0x7fffffff - 1) || 0x7fffffff < i - 1)));
    i = i - 1;
  }
  while((char)1);
  return 0;
}

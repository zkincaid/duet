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
  signed int c;
  i = 0;
  c = 0;
  for( ; !(i >= 11); c = c + 1)
  {
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
    i = i + 1;
    while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
  }
  return 0;
}

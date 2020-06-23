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
  signed int x=nondet_signed_int();
  c = 0;
  for( ; x >= 2 && !(x >= 100); c = c + 1)
  {
    while(!(!(x * x < (-0x7fffffff - 1) || 0x7fffffff < x * x)));
    x = x * x;
    while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
  }
  return 0;
}

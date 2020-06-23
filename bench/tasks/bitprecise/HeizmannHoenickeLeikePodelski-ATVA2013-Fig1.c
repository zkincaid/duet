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
  x = nondet_signed_int();
  y = 23;
  for( ; x >= 0; y = y + 1)
  {
    while(!(!(x - y < (-0x7fffffff - 1) || 0x7fffffff < x - y)));
    x = x - y;
    while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
  }
  return 0;
}

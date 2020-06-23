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
  y = nondet_signed_int();
  for( ; x >= 0 && !(x >= 1073741824); x = x - 1)
  {
    y = 1;
    for( ; !(y >= x); y = 2 * y)
      while(!(!(2 * y < (-0x7fffffff - 1) || 0x7fffffff < 2 * y)));
    while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
  }
  return 0;
}

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
  signed int tmp;
  signed int xtmp;
  x = nondet_signed_int();
  y = nondet_signed_int();
  for( ; x >= 1 && y >= 1; x = tmp)
  {
    tmp = y;
    xtmp = x;
    for( ; xtmp >= y && y >= 1; xtmp = xtmp - y)
      while(!(!(xtmp - y < (-0x7fffffff - 1) || 0x7fffffff < xtmp - y)));
    y = xtmp;
  }
  return 0;
}

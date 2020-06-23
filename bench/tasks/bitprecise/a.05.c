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
  signed int x;
  signed int y;
  x = nondet_signed_int();
  y = nondet_signed_int();
  c = 0;
  do
  {
    while(!(!(y < 2147483647) || (y < 2147483647)));
    if(!(x >= 1 + y) || y >= 2147483647)
      break;
    while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
    y = y + 1;
  }
  while((char)1);
  return 0;
}

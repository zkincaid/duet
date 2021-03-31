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
  signed int z;
  x = nondet_signed_int();
  y = 100;
  z = 1;
  for( ; x >= 0; z = -z)
  {
    while(!(!(x - y < (-0x7fffffff - 1) || 0x7fffffff < x - y)));
    x = x - y;
    while(!(!(y - z < (-0x7fffffff - 1) || 0x7fffffff < y - z)));
    y = y - z;
    while(!(!(z == -2147483648)));
  }
  return 0;
}

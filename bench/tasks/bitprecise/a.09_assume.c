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
  y = nondet_signed_int();
  z = nondet_signed_int();
  do
  {
    while(!(!(y > 0 && x >= z) || (y > 0 && x >= z)));
    if(!(2147483647 + -y >= z) || !(x >= z) || !(y >= 1))
      break;
    while(!(!(z + y < (-0x7fffffff - 1) || 0x7fffffff < z + y)));
    z = z + y;
  }
  while((char)1);
  return 0;
}

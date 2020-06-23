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
  signed int z;
  x = nondet_signed_int();
  y = nondet_signed_int();
  z = nondet_signed_int();
  c = 0;
  for( ; !(y >= x) && !(z >= x); z = z + 1)
  {
    while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
    y = y + 1;
    while(!(!(z + 1 < (-0x7fffffff - 1) || 0x7fffffff < z + 1)));
  }
  return 0;
}

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
  signed int tmp;
  x = nondet_signed_int();
  tmp = nondet_signed_int();
  do
  {
    while(!(!(x > 0 && tmp < 1073741824 && -1073741824 < tmp) || (x > 0 && tmp < 1073741824 && -1073741824 < tmp)));
    if(!(x == 2 * tmp) || !(tmp >= -1073741823) || !(x >= 1) || tmp >= 1073741824)
      break;
    while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
    x = x - 1;
    tmp = nondet_signed_int();
  }
  while((char)1);
  return 0;
}

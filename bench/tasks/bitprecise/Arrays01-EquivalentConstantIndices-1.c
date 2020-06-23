extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int a[1048l];
  signed int i=0;
  for( ; !(i >= 1048); i = i + 1)
  {
    a[(signed long int)i] = nondet_signed_int();
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
  }
  do
  {
    while(!(!(1 + 2 < (-0x7fffffff - 1) || 0x7fffffff < 1 + 2)));
    if(!(a[3l] >= 0))
      break;
    while(!(!(2 + 1 < (-0x7fffffff - 1) || 0x7fffffff < 2 + 1)));
    while(!(!(a[3l] - 1 < (-0x7fffffff - 1) || 0x7fffffff < a[3l] - 1)));
    a[3l] = a[(signed long int)(2 + 1)] - 1;
  }
  while((char)1);
  return 0;
}

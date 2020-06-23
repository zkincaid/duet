extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int f(signed int a);
signed int f(signed int a)
{
  signed int tmp;
  signed int count=0;
  for( ; a >= 2; count = count + 1)
  {
    tmp = a % 2;
    if(tmp == 0)
      a = a / 2;
    else
    {
      while(!(!(a - 1 < (-0x7fffffff - 1) || 0x7fffffff < a - 1)));
      a = a - 1;
    }
    while(!(!(count + 1 < (-0x7fffffff - 1) || 0x7fffffff < count + 1)));
  }
  return count;
}
signed int main()
{
  signed int x=nondet_signed_int();
  signed int count=f(x);
  return count;
}

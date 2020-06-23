extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int m;
  signed int n;
  signed int v1;
  signed int v2;
  n = nondet_signed_int();
  m = nondet_signed_int();
  if(m >= 1 && n >= 0)
  {
    v1 = n;
    v2 = 0;
    while(v1 >= 1)
      if(!(v2 >= m))
      {
        while(!(!(v2 + 1 < (-0x7fffffff - 1) || 0x7fffffff < v2 + 1)));
        v2 = v2 + 1;
        while(!(!(v1 - 1 < (-0x7fffffff - 1) || 0x7fffffff < v1 - 1)));
        v1 = v1 - 1;
      }
      else
        v2 = 0;
  }
  return 0;
}

extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int i;
  signed int j;
  signed int k;
  signed int m;
  signed int n;
  signed int N;
  i = nondet_signed_int();
  j = nondet_signed_int();
  k = nondet_signed_int();
  n = nondet_signed_int();
  m = nondet_signed_int();
  N = nondet_signed_int();
  if(N >= 0 && m >= 0 && n >= 0)
  {
    i = 0;
    for( ; !(i >= n); i = i + 1)
    {
      j = 0;
      for( ; !(j >= m); i = k)
      {
        while(!(!(j + 1 < (-0x7fffffff - 1) || 0x7fffffff < j + 1)));
        j = j + 1;
        k = i;
        do
        {
          while(!(!(N - 1 < (-0x7fffffff - 1) || 0x7fffffff < N - 1)));
          if(k >= -1 + N)
            break;
          while(!(!(k + 1 < (-0x7fffffff - 1) || 0x7fffffff < k + 1)));
          k = k + 1;
        }
        while((char)1);
      }
      while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
    }
  }
  return 0;
}

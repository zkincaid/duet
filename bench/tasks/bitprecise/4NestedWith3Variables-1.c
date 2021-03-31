extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int a;
  signed int b;
  signed int q;
  signed int olda;
  q = nondet_signed_int();
  a = nondet_signed_int();
  b = nondet_signed_int();
  if(!(q >= -524287) || q >= 524288)
    return 0;
  else
    if(!(a >= -524287) || a >= 524288)
      return 0;
    else
      if(!(b >= -524287) || b >= 524288)
        return 0;
      else
      {
        for( ; q >= 1; b = 4 * olda + 3 * b)
        {
          while(!(!(q + a < (-0x7fffffff - 1) || 0x7fffffff < q + a)));
          while(!(!(a + q - 1 < (-0x7fffffff - 1) || 0x7fffffff < a + q - 1)));
          q = (q + a) - 1;
          olda = a;
          while(!(!(3 * olda < (-0x7fffffff - 1) || 0x7fffffff < 3 * olda)));
          while(!(!(4 * b < (-0x7fffffff - 1) || 0x7fffffff < 4 * b)));
          while(!(!(3 * olda - 4 * b < (-0x7fffffff - 1) || 0x7fffffff < 3 * olda - 4 * b)));
          a = 3 * olda - 4 * b;
          while(!(!(4 * olda < (-0x7fffffff - 1) || 0x7fffffff < 4 * olda)));
          while(!(!(3 * b < (-0x7fffffff - 1) || 0x7fffffff < 3 * b)));
          while(!(!(4 * olda + 3 * b < (-0x7fffffff - 1) || 0x7fffffff < 4 * olda + 3 * b)));
        }
        return 0;
      }
}

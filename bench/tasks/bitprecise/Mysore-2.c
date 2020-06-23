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
  signed int x=nondet_signed_int();
  c = nondet_signed_int();
  if(!(x >= -65535) || x >= 65536)
    return 0;
  else
    if(!(c >= -65535) || c >= 65536)
      return 0;
    else
    {
      if(c >= 2)
        do
        {
          while(!(!(x + c < (-0x7fffffff - 1) || 0x7fffffff < x + c)));
          if(!(c + x >= 0))
            break;
          while(!(!(x - c < (-0x7fffffff - 1) || 0x7fffffff < x - c)));
          x = x - c;
          while(!(!(c + 1 < (-0x7fffffff - 1) || 0x7fffffff < c + 1)));
          c = c + 1;
        }
        while((char)1);
      return 0;
    }
}

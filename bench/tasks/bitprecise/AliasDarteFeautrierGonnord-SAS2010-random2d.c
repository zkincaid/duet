extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int N;
  signed int x;
  signed int y;
  signed int i;
  signed int r;
  N = 10;
  x = 0;
  y = 0;
  i = 0;
  while(!(i >= N))
  {
    while(!(!(i + 1 < (-0x7fffffff - 1) || 0x7fffffff < i + 1)));
    i = i + 1;
    r = nondet_signed_int();
    if(r >= 0 && !(r >= 4))
    {
      if(r == 0)
      {
        while(!(!(x + 1 < (-0x7fffffff - 1) || 0x7fffffff < x + 1)));
        x = x + 1;
      }
      else
        if(r == 1)
        {
          while(!(!(x - 1 < (-0x7fffffff - 1) || 0x7fffffff < x - 1)));
          x = x - 1;
        }
        else
          if(r == 2)
          {
            while(!(!(y + 1 < (-0x7fffffff - 1) || 0x7fffffff < y + 1)));
            y = y + 1;
          }
          else
            if(r == 3)
            {
              while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
              y = y - 1;
            }
    }
  }
  return 0;
}

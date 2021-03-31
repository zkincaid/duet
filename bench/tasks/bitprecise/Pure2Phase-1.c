extern int __VERIFIER_nondet_int();
extern void __VERIFIER_assume(int);
int nondet_signed_int() {
  int r = __VERIFIER_nondet_int();
  __VERIFIER_assume ((-0x7fffffff - 1) <= r && r <= 0x7fffffff);
  return r;
}
signed int main()
{
  signed int y;
  signed int z;
  y = nondet_signed_int();
  z = nondet_signed_int();
  if(!(y >= -1073741823) || y >= 1073741824)
    return 0;
  else
    if(z >= 1073741824)
      return 0;
    else
    {
      while(z >= 0)
      {
        while(!(!(y - 1 < (-0x7fffffff - 1) || 0x7fffffff < y - 1)));
        y = y - 1;
        if(y >= 0)
        {
          z = nondet_signed_int();
          if(z >= 1073741824)
            return 0;
        }
        else
        {
          while(!(!(z - 1 < (-0x7fffffff - 1) || 0x7fffffff < z - 1)));
          z = z - 1;
        }
      }
      return 0;
    }
}

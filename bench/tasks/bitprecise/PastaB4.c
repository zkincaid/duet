signed int main()
{
  signed int x;
  signed int y;
  signed int t;
  x = nondet_signed_int();
  y = nondet_signed_int();
  for( ; !(y >= x); y = t)
  {
    t = x;
    x = y;
  }
  return 0;
}

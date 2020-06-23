signed int main()
{
  signed int x;
  signed int y;
  signed int tmp;
  x = nondet_signed_int();
  y = nondet_signed_int();
  tmp = nondet_signed_int();
  for( ; !(y >= x); y = tmp)
  {
    tmp = x;
    x = y;
  }
  return 0;
}

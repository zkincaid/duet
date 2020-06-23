signed int main()
{
  signed int i;
  signed int x;
  signed int y;
  i = nondet_signed_int();
  x = 0;
  y = 0;
  if(i >= 11)
    x = 1;
  else
    y = 1;
  while(x == y)
    ;
  return 0;
}

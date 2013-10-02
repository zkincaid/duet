void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}

void foo()
{
  int y=0;
  int c1=rand(), c2=rand();
  if (c1) y++;
  if (c2) y--;
  else y+=10;
}

void main()
{
  int d = 1;
  int x;
  int c1=rand(), c2=rand();

  if (c1) d = d - 1;
  if (c2) foo();

  c1=rand(), c2=rand();

  if (c1) foo();
  if (c2) d = d - 1;
  
  while(x>0)
  {
    x=x-d;
  }

  assert(x<=0);
}

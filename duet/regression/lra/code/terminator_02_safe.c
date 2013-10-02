extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
int __VERIFIER_nondet_int();
_Bool __VERIFIER_nondet_bool();

void main()
{
  int x=rand();
  int y=rand();
  int z=rand();
  assume(x<100);
  assume(z<100);
  while(x<100 && 100<z) {
      int tmp=rand();
      if (tmp) {
	  x++;
      }
      else {
	  x--;
	  z--;
      }
  }                   
    
  assert(x>=100 || z<=100);
}

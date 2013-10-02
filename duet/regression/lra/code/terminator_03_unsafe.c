void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
extern int __VERIFIER_nondet_int();

void main() {
    int x=rand();
    int y=rand();

    if (y>0) {
	while(x<100)  {
	    x=x+y;
	}
    }                           
    assert(y<=0 || (y<0 && x>=100));     
}



void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
_Bool __VERIFIER_nondet_bool();
int __VERIFIER_nondet_int();

//x is an input variable
int x;

void foo() {
  x--;
}

void main() {
    x=rand();
    assume(x >= 0);
    while (x > 0) {
	int c = rand();
	if(c) foo();
	else foo();
    }
    assert(x==0);
}




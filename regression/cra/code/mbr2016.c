// Source: Antoine Miné, Jason Breck, Thomas Reps: An Algorithm
// Inspired by Constraint Solvers to Infer Inductive Invariants in
// Numeric Programs, ESOP 2016.

void rotate(float x, float y) {
  while(__VERIFIER_nondet()) {
    float xp,yp;
    xp = 0.68*(x-y);
    yp = 0.68*(x+y);
    x = xp;
    y = yp;
  }
  __VERIFIER_assert(-2 <= x && x <= 2);
  __VERIFIER_assert(-2 <= y && y <= 2);
}

void main() {
  float x,y;
  __VERIFIER_assume(-1 <= x && x <= 1);
  __VERIFIER_assume(-1 <= y && y <= 1);
  rotate(x, y);
}

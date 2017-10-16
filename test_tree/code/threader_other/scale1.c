// #include <assert.h>
#include <pthread.h>

int g;

void* thr1(void* arg) {
  int l;
  glb_init(g>=0);
  glb_init(l==0);
  while (l < g) {
    l = l + 1;
  }
  assert(l <= g);
  return NULL;
}

/* Minimal set of predicates (inferred automatically in 3 iterations) 2-2/1-1/0-0:
retractall(preds(_,_,_)), retractall(trans_preds(_,_,_,_)),
assert(preds(1, p(_,data(G,L1,_)), [G-L1>=0,G-L1>=1])),
assert(preds(2, p(_,data(G,_,L2)), [G-L2>=0,G-L2>=1])),

assert(trans_preds(_-1, p(_,data(G,L1,_)), p(_,data(GP,L1P,_)), [G-GP=<0])),
assert(trans_preds(_-2, p(_,data(G,_,L2)), p(_,data(GP,_,L2P)), [G-GP=<0])).
*/

void main(){

  int n;
  for (int i = 0; i < n; ++i){
    pthread_t t;
    pthread_create(&t, NULL, thr1, NULL);
  }
}

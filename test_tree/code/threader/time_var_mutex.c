#include<pthread.h>

int block;
int busy; // boolean flag indicating whether the block has be an allocated to an inode
int inode;
int m_inode=0; // protects the inode
int m_busy=0; // protects the busy flag

#define acquire(l) \
  __VERIFIER_atomic_begin(); \
  assume (l == 0); \
  l = 1; \
  __VERIFIER_atomic_end()

#define release(l) \
  __VERIFIER_atomic_begin(); \
  assert (l == 1); \
  l = 0; \
  __VERIFIER_atomic_end()

void* thr1(void* arg){
  glb_init(inode == busy);
  acquire(m_inode);
  if(inode == 0){
    acquire(m_busy);
    busy = 1;
    release(m_busy);
    inode = 1;
  }
  block = 1;
  assert(block == 1);
  release(m_inode);
  return NULL;
}

void* thr2(void* arg){
  acquire(m_busy);
  if(busy == 0){
    block = 0;
    assert(block == 0);
  }
  release(m_busy);
  return NULL;
}

void main(){
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thr1, NULL);
  pthread_create(&t2, NULL, thr2, NULL);
}

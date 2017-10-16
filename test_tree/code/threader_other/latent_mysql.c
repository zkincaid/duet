#include<pthread.h>

int table_master = 1;
int table_slave = 1;
int binlog;
int can_start_m = 0, done_m = 0;
int can_start_s = 0, done_s = 0;
int can_start_c = 0, done_c = 0;
int res1, res2;

int nondet(){
  int n;
  return n;
}

void* t1_master(void* arg) {
  assume(can_start_m >= 1);
  table_master = 3;
  binlog = 1;
  done_m++;
  return NULL;
}

void* t2_master(void* arg) {
  assume(can_start_m >= 1);
  table_master = 5;
  binlog = 2;
  done_m++;
  return NULL;
}

void* slave(void* arg) {
  assume(can_start_s > 0);
  if (binlog <= 1) {
    table_slave = 5;
    table_slave = 3;
  } else {
    table_slave = 3;
    table_slave = 5;
  }
  done_s++;
  return NULL;
}

void* client_from_master(void* arg) {
  assume(can_start_c >= 1);
  // read from the master
  res1 = table_master;
  done_c=done_c+1;
  return NULL;
}

void* client_from_slave(void* arg) {
  assume(can_start_c >= 1);
  // read from the slave
  res2 = table_slave;
  done_c=done_c+1;
  return NULL;
}

void main() { // complete code for the main thread
  pthread_t t1, t2, t3, t4;

  can_start_m = 2;
  // fork (t1_master || t2_master);
  if (nondet()){
    pthread_create(&t1, NULL, t1_master, NULL);
  } else {
    pthread_create(&t1, NULL, t2_master, NULL);
  }
  assume(done_m >= 2);
  can_start_s = 1;
  // fork slave;
  pthread_create(&t2, NULL, slave, NULL);
  assume(done_s >= 1);
  can_start_c = 2;
  // fork client_from_master(res1);
  pthread_create(&t3, NULL, client_from_master, NULL);
  // fork client_from_slave(res);
  pthread_create(&t4, NULL, client_from_slave, NULL);
  assume(done_c >= 1);
  assert(res1 == res2);
}

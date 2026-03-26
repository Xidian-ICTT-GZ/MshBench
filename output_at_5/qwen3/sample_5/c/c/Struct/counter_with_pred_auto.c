#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate counter(struct Counter* c, int v) =
  c != null &*&
  c->value == v;
@*/

//@ requires true;
//@ ensures \result != null &*& counter(\result, v);
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  open counter(c, v);
  close counter(c, v);
  return c;
}

//@ requires c != null &*& counter(c, v);
//@ ensures c != null &*& counter(c, v + 1);
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

//@ requires c != null &*& counter(c, _);
//@ ensures true;
void dispose(struct Counter* c)
{
  free(c);
}

//@ requires c1 != null &*& c2 != null &*& counter(c1, v1) &*& counter(c2, v2);
//@ ensures c1 != null &*& c2 != null &*& counter(c1, v2) &*& counter(c2, v1);
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

//@ requires c != null &*& counter(c, v);
//@ ensures \result == v;
int get(struct Counter* c)
{
  return c->value;
}

//@ requires true;
//@ ensures true;
int main() 
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  open counter(c1, 0);
  open counter(c2, 5);
  
  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);
  assert(tmp == 1);
  
  close counter(c1, 0);
  close counter(c2, 5);
  
  dispose(c1); dispose(c2);
  return 0;
}
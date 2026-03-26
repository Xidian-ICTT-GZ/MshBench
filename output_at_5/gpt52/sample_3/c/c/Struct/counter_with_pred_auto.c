#include "stdlib.h"

struct Counter {
  int value;
};

/*@
predicate counter(struct Counter* c; int v) =
  malloc_block_Counter(c) &*& c->value |-> v;
@*/

struct Counter* init(int v)
  //@ requires true;
  //@ ensures counter(result, v);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close counter(c, v);
  return c;
}

void increment(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v + 1);
{
  //@ open counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close counter(c, v + 1);
}

void dispose(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures true;
{
  //@ open counter(c, v);
  free(c);
}

void swap(struct Counter* c1, struct Counter* c2)
  //@ requires counter(c1, ?v1) &*& counter(c2, ?v2) &*& c1 != c2;
  //@ ensures counter(c1, v2) &*& counter(c2, v1);
{
  //@ open counter(c1, v1);
  //@ open counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close counter(c1, v2);
  //@ close counter(c2, v1);
}

int get(struct Counter* c)
  //@ requires counter(c, ?v);
  //@ ensures counter(c, v) &*& result == v;
{
  //@ open counter(c, v);
  int r = c->value;
  //@ close counter(c, v);
  return r;
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  assert(tmp == 1);
  
  dispose(c1); dispose(c2);
  return 0;
}
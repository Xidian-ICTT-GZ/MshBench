#include "stdlib.h"

struct Counter
{
  int value;
};

/*@ predicate counter(struct Counter *c; int v) = c->value |-> v; @*/

/*@ requires malloc_block(c, sizeof(struct Counter)); @*/
/*@ ensures counter(result, v) &*& result != 0; @*/
struct Counter *init(int v)
{
  struct Counter *c = malloc(sizeof(struct Counter));
  if (c == 0)
  {
    abort();
  }
  c->value = v;
  /*@ close counter(c, v); @*/
  return c;
}

/*@ requires counter(c, ?v); @*/
/*@ ensures counter(c, v + 1); @*/
void increment(struct Counter *c)
{
  /*@ open counter(c, v); @*/
  int tmp = c->value;
  c->value = tmp + 1;
  /*@ close counter(c, v + 1); @*/
}

/*@ requires counter(c, ?v); @*/
/*@ ensures true; @*/
void dispose(struct Counter *c)
{
  /*@ open counter(c, v); @*/
  free(c);
}

/*@ requires counter(c1, ?v1) &*& counter(c2, ?v2); @*/
/*@ ensures counter(c1, v2) &*& counter(c2, v1); @*/
void swap(struct Counter *c1, struct Counter *c2)
{
  /*@ open counter(c1, v1); @*/
  /*@ open counter(c2, v2); @*/
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  /*@ close counter(c1, v2); @*/
  /*@ close counter(c2, v1); @*/
}

/*@ requires counter(c, ?v); @*/
/*@ ensures counter(c, v) &*& result == v; @*/
int get(struct Counter *c)
{
  /*@ open counter(c, v); @*/
  int tmp = c->value;
  /*@ close counter(c, v); @*/
  return tmp;
}

/*@ requires true; @*/
/*@ ensures true; @*/
int main()
{
  struct Counter *c1 = init(0);
  struct Counter *c2 = init(5);

  increment(c1);
  swap(c1, c2);
  int tmp = get(c2);

  dispose(c1);
  dispose(c2);
  return 0;
}
#include "stdlib.h"

/*@
predicate Counter(struct Counter* c, int v) =
  c != null &*&
  c->value == v;
@*/

struct Counter {
  int value;
};

//@ requires true;
//@ ensures \result != null &*& Counter(\result, v);
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  
  return c;
}

//@ requires Counter(c, v);
//@ ensures Counter(c, v + 1);
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

//@ requires Counter(c, _);
//@ ensures true;
void dispose(struct Counter* c)
{
  free(c);
}

//@ requires Counter(c1, v1) &*& Counter(c2, v2);
//@ ensures Counter(c1, v2) &*& Counter(c2, v1);
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

//@ requires Counter(c, v);
//@ ensures \result == v;
int get(struct Counter* c)
{
  int tmp = c->value;
  
  return tmp;
}

int main() 
{
  struct Counter* c1 = init(0); 
  struct Counter* c2 = init(5);

  increment(c1); 
  swap(c1, c2); 
  int tmp = get(c2);
  
  dispose(c1); 
  dispose(c2);
  return 0;
}
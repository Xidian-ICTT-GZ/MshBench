#include "stdlib.h"

struct Counter {
  int value;
};

//@ predicate Counter(struct Counter* c; int v) = c->value |-> v &*& malloc_block_Counter(c);

/*@
requires true;
ensures Counter(result, v);
@*/
struct Counter* init(int v)
  
  
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  //@ close Counter(c, _);
  c->value = v;
  //@ close Counter(c, v);

  
  return c;
}

/*@
requires Counter(c, ?v);
ensures Counter(c, v+1);
@*/
void increment(struct Counter* c)
  
  
{
  //@ open Counter(c, ?old);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, old+1);
  
}

/*@
requires Counter(c, _);
ensures true;
@*/
void dispose(struct Counter* c)
  
  
{
  //@ open Counter(c, _);
  free(c);
}

/*@
requires Counter(c1, ?v1) &*& Counter(c2, ?v2);
ensures Counter(c1, v2) &*& Counter(c2, v1);
@*/
void swap(struct Counter* c1, struct Counter* c2)
  
  
{
  //@ open Counter(c1, v1);
  //@ open Counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close Counter(c1, v2);
  //@ close Counter(c2, v1);
  
  
}

/*@
requires Counter(c, ?v);
ensures Counter(c, v) &*& result == v;
@*/
int get(struct Counter* c)
  
  
{
  //@ open Counter(c, ?v);
  int tmp = c->value;
  //@ close Counter(c, v);
  return tmp;
}

/*@
requires true;
ensures true;
@*/
int main() 
  
  
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);
  //@ assert Counter(c1, 0) &*& Counter(c2, 5);

  increment(c1); 
  //@ assert Counter(c1, 1) &*& Counter(c2, 5);
  swap(c1, c2); 
  //@ assert Counter(c1, 5) &*& Counter(c2, 1);
  int tmp = get(c2);
  //@ assert tmp == 1;
  
  dispose(c1); dispose(c2);
  return 0;
}
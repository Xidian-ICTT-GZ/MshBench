#include "stdlib.h"

/*@
predicate myStruct_pred(struct myStruct* ms; int i, short s, char c) = 
  ms->i |-> i &*& ms->s |-> s &*& ms->c |-> c;
@*/

struct myStruct {
  int i;
  short s;
  char c;
};

void m(int i, short s, char c)
  //@ requires true;
  //@ ensures true;
{
  short r = 354;
  //@ assume (354 + i) <= INT_MAX && (354 + i) >= INT_MIN; // to avoid overflow proof error
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ close myStruct_pred(ms, 0, 0, 0);
  ms->c = 0;
  //@ open myStruct_pred(ms, 0, 0, 0);
  ms->i = i;
  ms->s = ms->c;
  //@ close myStruct_pred(ms, i, ms->s, ms->c);
  free(ms);
}
#include "stdlib.h"

/*@
predicate myStruct_pred(struct myStruct* ms;) =
  ms->i |-> _ &*& ms->s |-> _ &*& ms->c |-> _;
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
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ close myStruct_pred(ms);
  ms->c = 0;
  //@ open myStruct_pred(ms);
  ms->i = i;
  ms->s = ms->c;
  //@ close myStruct_pred(ms);
  free(ms);
}
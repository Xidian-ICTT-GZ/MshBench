#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

/*@
predicate myStruct(struct myStruct *ms; int i, short s, char c) =
  ms->i |-> i &*& ms->s |-> s &*& ms->c |-> c &*& malloc_block_myStruct(ms);
@*/

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
  //@ close myStruct(ms, _, _, _);
  ms->c = 0;
  //@ open myStruct(ms, _, _, _);
  //@ close myStruct(ms, _, _, 0);
  ms->i = i;
  //@ open myStruct(ms, _, _, _);
  //@ close myStruct(ms, i, _, _);
  ms->s = ms->c;
  //@ open myStruct(ms, i, _, c0);
  //@ close myStruct(ms, i, c0, c0);
  //@ open myStruct(ms, i, c0, c0);
  free(ms);
}
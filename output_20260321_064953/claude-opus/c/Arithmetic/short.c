#include "stdlib.h"

/*@
predicate myStruct(struct myStruct* ms; int i, short s, char c) =
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
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ close myStruct(ms, _, _, _);
  ms->c = 0;
  //@ open myStruct(ms, _, _, _);
  ms->i = i;
  ms->s = ms->c;
  //@ close myStruct(ms, ms->i, ms->s, ms->c);
  //@ open myStruct(ms, _, _, _);
  free(ms);
}
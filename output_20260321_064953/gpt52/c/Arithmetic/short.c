#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

/*@
predicate myStruct(struct myStruct *p; int i, short s, char c) =
  p->i |-> i &*& p->s |-> s &*& p->c |-> c;
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
  //@ assume(ms != 0);
  if(ms == 0) abort();
  //@ close_struct(ms);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ open_struct(ms);
  free(ms);
}
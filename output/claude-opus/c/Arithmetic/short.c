#include "stdlib.h"

struct myStruct
{
  int i;
  short s;
  char c;
};

/*@
predicate myStruct_fields(struct myStruct *ms; int i, short s, char c) =
  ms->i |-> i &*& ms->s |-> s &*& ms->c |-> c;
@*/

void m(int i, short s, char c)
//@ requires true;
//@ ensures true;
{
  short r = 354;
  r += i;
  int j = s;
  r = (short)i;
  struct myStruct *ms = malloc(sizeof(struct myStruct));
  if (ms == 0)
    abort();
  //@ open chars((void *)ms, sizeof(struct myStruct), _);
  //@ close_struct(ms);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ open_struct(ms);
  //@ close chars((void *)ms, sizeof(struct myStruct), _);
  free(ms);
}
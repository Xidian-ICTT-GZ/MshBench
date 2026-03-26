#include "stdlib.h"

struct myStruct
{
  int i;
  short s;
  char c;
};

//@ predicate myStruct_valid(struct myStruct *ms) = ms->i |-> _ &*& ms->s |-> _ &*& ms->c |-> _;

//@ requires true;
//@ ensures true;
void m(int i, short s, char c)
{
  short r = 354;
  r += i;
  int j = s;
  r = (short)i;
  struct myStruct *ms = malloc(sizeof(struct myStruct));
  //@ assert ms != 0;
  if (ms == 0)
    abort();
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  free(ms);
}
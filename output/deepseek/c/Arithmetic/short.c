#include "stdlib.h"

struct myStruct
{
  int i;
  short s;
  char c;
};

/*@
predicate myStruct(struct myStruct *ms; int vi, short vs, char vc) =
  ms->i |-> vi &*& ms->s |-> vs &*& ms->c |-> vc;
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
  //@ close myStruct(ms, _, _, _);
  ms->c = 0;
  //@ open myStruct(ms, _, _, _);
  //@ close myStruct(ms, _, _, 0);
  ms->i = i;
  //@ open myStruct(ms, _, _, _);
  //@ close myStruct(ms, i, _, _);
  ms->s = ms->c;
  //@ open myStruct(ms, _, _, _);
  //@ close myStruct(ms, i, 0, _);
  //@ open myStruct(ms, _, _, _);
  free(ms);
}
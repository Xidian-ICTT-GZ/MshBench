#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

/*@ predicate myStructp(struct myStruct *p; int i, short s, char c) =
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
  if(ms == 0) abort();
  //@ close myStructp(ms, _, _, _);
  //@ open myStructp(ms, _, _, _);
  ms->c = 0;
  //@ close myStructp(ms, _, _, _);
  //@ open myStructp(ms, _, _, _);
  ms->i = i;
  //@ close myStructp(ms, _, _, _);
  //@ open myStructp(ms, _, _, _);
  ms->s = ms->c;
  //@ close myStructp(ms, _, _, _);
  //@ open myStructp(ms, _, _, _);
  free(ms);
}
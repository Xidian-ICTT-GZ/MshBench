#include "stdlib.h"

struct myStruct
{
  int i;
  short s;
  char c;
};

/*@ predicate myStruct(struct myStruct *p; int i, short s, char c) =
    p != 0 &*& valid(p) &*&
    p->i |-> i &*& p->s |-> s &*& p->c |-> c;
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
  //@ if (ms != 0) { assert malloc_block_myStruct(ms); }
  //@ if (ms == 0) { assert true; }
  if (ms == 0)
    abort();
  //@ open true;
  //@ assert malloc_block_myStruct(ms);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ close myStruct(ms, ms->i, ms->s, ms->c);
  //@ open myStruct(ms, ms->i, ms->s, ms->c);
  free(ms);
}
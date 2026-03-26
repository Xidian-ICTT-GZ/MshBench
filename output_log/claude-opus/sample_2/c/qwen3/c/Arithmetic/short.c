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

{
  short r = 354;
  r += i;
  int j = s;
  r = (short)i;
  struct myStruct *ms = malloc(sizeof(struct myStruct));
  //@ requires true;
  //@ ensures ms != 0 ? myStruct(ms; _, _, _) : ms == 0;
  if (ms == 0)
    abort();
  //@ requires ms != 0 &*& malloc_block_myStruct(ms);
  //@ ensures myStruct(ms; _, _, _);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ requires myStruct(ms; _, _, _);
  //@ ensures true;
  free(ms);
}
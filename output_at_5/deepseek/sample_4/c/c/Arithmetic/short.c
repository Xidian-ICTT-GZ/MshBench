#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

/*@
predicate myStruct(struct myStruct *s;) = s->i |-> _ &*& s->s |-> _ &*& s->c |-> _;
@*/

void m(int i, short s, char c)
  //@ requires -32768 <= i && i <= 32767;
  //@ ensures true;
{
  short r = 354;
  //@ assert -32768 <= 354 + i && 354 + i <= 32767;
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ close myStruct(ms);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ open myStruct(ms);
  free(ms);
}
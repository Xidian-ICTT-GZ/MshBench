#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

/*@
predicate myStruct(struct myStruct *s;) =
  s->i |-> ?i &*& s->s |-> ?sval &*& s->c |-> ?c;
@*/

//@ requires true;
//@ ensures true;
void m(int i, short s, char c)
  
  
{
  short r = 354;
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ close myStruct(ms);
  ms->c = 0;
  //@ open myStruct(ms);
  //@ close myStruct(ms);
  ms->i = i;
  //@ open myStruct(ms);
  //@ close myStruct(ms);
  ms->s = ms->c;
  //@ open myStruct(ms);
  free(ms);
}
#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

//@ predicate struct_myStruct(struct myStruct* ms) = true;

void m(int i, short s, char c)
  
  
{
  short r = 354;
  r += i;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  //@ open struct_myStruct(ms);
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  //@ close struct_myStruct(ms);
  free(ms);
}
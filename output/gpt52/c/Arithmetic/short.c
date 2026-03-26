#include "stdlib.h"

struct myStruct
{
  int i;
  short s;
  char c;
};

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
  //@ assert ms != 0;
  ms->c = 0;
  ms->i = i;
  ms->s = ms->c;
  free(ms);
}
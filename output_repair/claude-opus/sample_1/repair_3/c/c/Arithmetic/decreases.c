#include "stdio.h"

void m(int i)
//@ requires i <= 10;
//@ ensures true;
{
  while (i < 10)
  //@ invariant i <= 10;
  {
    i = i + 1;
  }
}

int main()
//@ requires true;
//@ ensures true;
{
  m(0);
  return 0;
}
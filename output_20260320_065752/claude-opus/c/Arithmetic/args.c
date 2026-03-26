#include "stdio.h"

//@ requires true;
//@ ensures true;
int main(int argc, char **argv) 
{
  //@ int i = 0;
  for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i && i <= argc;
  {
    //@ assert argv != 0;
    //@ assert argv[i] != 0;
    puts(*(argv + i));
  }
  
  return 0;
}
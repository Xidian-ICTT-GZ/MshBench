#include "stdio.h"

/*@ predicate argv_valid(char **argv, int argc) = 
  argc >= 0 &*& chars(argv, argc, _); @*/

int main(int argc, char **argv)
//@ requires argv_valid(argv, argc);
//@ ensures true;
{
  for (int i = 0; i < argc; i++)
  //@ invariant 0 <= i &*& i <= argc &*& argv_valid(argv, argc);
  {
    puts(*(argv + i));
  }

  return 0;
}
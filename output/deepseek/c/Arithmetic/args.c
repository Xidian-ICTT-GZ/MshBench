#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ?
        emp
    :
        argv[0] |-> ?s &*& [?f]string(s, ?cs) &*& argv_chars(argv + 1, argc - 1);
@*/

int main(int argc, char **argv)
//@ requires argc >= 0 &*& argv_chars(argv, argc);
//@ ensures true;
{
  for (int i = 0; i < argc; i++)
  //@ invariant 0 <= i &*& i <= argc &*& argv_chars(argv + i, argc - i);
  {
    //@ open argv_chars(argv + i, argc - i);
    puts(*(argv + i));
    //@ close argv_chars(argv + i + 1, argc - i - 1);
  }
  //@ open argv_chars(argv + argc, 0);
  return 0;
}
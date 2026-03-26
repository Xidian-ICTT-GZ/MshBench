#include "stdio.h"

/*@
predicate argv_array(char **argv, int argc, int i) =
  i >= argc ?
    true
  :
    pointer(argv + i, ?s) &*& string(s, ?cs) &*& argv_array(argv, argc, i + 1);
@*/

int main(int argc, char **argv)
  //@ requires argv_array(argv, argc, 0);
  //@ ensures true;
{
  for (int i = 0; i < argc; i++)
    //@ invariant argv_array(argv, argc, i) &*& i >= 0 &*& i <= argc;
  {
    //@ open argv_array(argv, argc, i);
    puts(*(argv + i));
    //@ close argv_array(argv, argc, i + 1);
  }
  //@ open argv_array(argv, argc, argc);
  return 0;
}
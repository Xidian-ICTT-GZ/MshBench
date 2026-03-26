#include "stdio.h"

/*@
predicate argv_args(char **argv, int argc) =
  argc == 0 ? emp : argv[0] |-> ?s &*& argv_args(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
//@ requires argv_args(argv, argc);
//@ ensures argv_args(argv, argc);
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i && i <= argc &*& argv_args(argv + i, argc - i);
    {
        puts(*(argv + i));
    }
    return 0;
}
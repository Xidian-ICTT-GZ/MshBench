#include "stdio.h"

/*@
predicate argv_strs(char **argv, int argc) =
  argc == 0 ? emp :
  argv + 0 |-> ?p &*& string(p) &*& argv_strs(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires argv_strs(argv, argc);
    //@ ensures argv_strs(argv, argc);
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i && i <= argc &*& argv_strs(argv, argc);
    {
        puts(*(argv + i));
    }
    
    return 0;
}
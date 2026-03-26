#include "stdio.h"

/*@
predicate argv(char **argv, int argc) =
    argc == 0 ? emp : string(argv, ?cs) &*& argv(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires argv(argv, argc);
    //@ ensures true;
{
    //@ open argv(argv, argc);
    for (int i = 0; i < argc; i++)
        //@ invariant argv(argv, argc) &*& 0 <= i &*& i <= argc;
    {
        //@ open argv(argv + i, argc - i);
        //@ assert string(argv + i, ?cs);
        puts(*(argv + i));
        //@ close argv(argv + i, argc - i);
    }
    //@ close argv(argv, argc);
    return 0;
}
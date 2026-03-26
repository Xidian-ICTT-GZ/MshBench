#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ? true : string(argv[0], ?cs) &*& argv_chars(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires true;
    //@ ensures true;
{
    //@ assume(argv_chars(argv, argc));
    for (int i = 0; i < argc; i++)
        //@ invariant argv_chars(argv, argc) &*& 0 <= i &*& i <= argc;
    {
        //@ open argv_chars(argv + i, argc - i);
        //@ assert string(*(argv + i), ?cs);
        puts(*(argv + i));
        //@ close argv_chars(argv + i, argc - i);
    }
    return 0;
}
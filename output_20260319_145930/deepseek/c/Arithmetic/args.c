#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ? true : malloc_block_chars(argv, 1) &*& string(argv, ?s) &*& argv_chars(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires argc >= 0 &*& argv_chars(argv, argc);
    //@ ensures true;
{
    //@ open argv_chars(argv, argc);
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv_chars(argv + i, argc - i);
    {
        //@ open argv_chars(argv + i, argc - i);
        //@ assert string(*(argv + i), ?s);
        puts(*(argv + i));
        //@ close argv_chars(argv + i, argc - i);
    }
    //@ close argv_chars(argv + argc, 0);
    return 0;
}
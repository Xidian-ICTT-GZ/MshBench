#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ?
        true
    :
        argv[0] |-> ?s &*& [?f]string(s, ?cs) &*& argv_chars(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires argv_chars(argv, argc);
    //@ ensures true;
{
    //@ open argv_chars(argv, argc);
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv_chars(argv + i, argc - i);
    {
        //@ open argv_chars(argv + i, argc - i);
        //@ assert argv[i] |-> ?s;
        //@ string_to_chars(s);
        puts(*(argv + i));
        //@ chars_to_string(s);
        //@ close argv_chars(argv + i, argc - i);
    }
    //@ close argv_chars(argv + argc, 0);
    return 0;
}
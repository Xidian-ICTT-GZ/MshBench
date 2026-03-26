#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ? true : character(argv, ?c) &*& argv_chars(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires true;
    //@ ensures true;
    
{
    //@ open main_pre();
    //@ close argv_chars(argv, argc);
    //@ int i = 0;
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i && i <= argc &*& argv_chars(argv + i, argc - i);
        
    {
        //@ open argv_chars(argv + i, argc - i);
        //@ assert character(argv + i, ?c);
        //@ close argv_chars(argv + i, argc - i);
        puts(*(argv + i));
    }
    //@ close main_pre();
    return 0;
}
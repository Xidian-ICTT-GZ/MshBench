#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc == 0 ?
        true
    :
        malloc_block(argv, argc) &*&
        chars(argv[0], ?n0, _) &*&
        argv_chars(argv + 1, argc - 1);
@*/

//@ requires argc >= 0 &*& [_]argv_chars(argv, argc);
//@ ensures true;
int main(int argc, char **argv) 
    
    
{
    //@ open argv_chars(argv, argc);
    for (int i = 0; i < argc; i++)
        
    {
        //@ open argv_chars(argv + i, argc - i);
        
        
        puts(*(argv + i));
        //@ close argv_chars(argv + i + 1, argc - i - 1);
    }
    //@ close argv_chars(argv + argc, 0);
    
    return 0;
}
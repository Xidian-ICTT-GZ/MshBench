#include "stdio.h"

/*@
predicate argv_block(char **argv, int argc) =
    argc <= 0 ? true : pointer(argv, ?arg) &*& argv_block(argv + 1, argc - 1);
@*/
int main(int argc, char **argv) 
    
//@ requires 0 <= argc &*& argv_block(argv, argc);
//@ ensures argv_block(argv, argc);
    
{
    for (int i = 0; i < argc; i++)
        
        //@ invariant 0 <= i &*& i <= argc &*& argv_block(argv, argc);
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

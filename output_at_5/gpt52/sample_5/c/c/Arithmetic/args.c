#include "stdio.h"

/*@
predicate argv_array(char **argv, int argc) =
    argc <= 0 ?
        true
    :
        argv[0] |-> ?s &*& argv_array(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires 0 <= argc &*& argv_array(argv, argc);
    //@ ensures true;
    
    
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv_array(argv, argc);
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}
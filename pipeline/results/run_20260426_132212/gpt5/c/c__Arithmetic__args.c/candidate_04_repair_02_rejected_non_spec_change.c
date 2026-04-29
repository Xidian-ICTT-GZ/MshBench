#include "stdio.h"

int main(int argc, char **argv) 
//@ requires argv[..argc] |-> ?args;
    
    
//@ ensures argv[..argc] |-> args;
{
    //@ if (0 <= argc) {} else { assume(false); }
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv[..argc] |-> args;
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

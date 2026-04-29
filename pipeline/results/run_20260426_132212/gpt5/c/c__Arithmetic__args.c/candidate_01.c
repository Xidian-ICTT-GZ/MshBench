#include "stdio.h"

//@ requires argc >= 0 &*& argv[..argc] |-> ?args;
//@ ensures argv[..argc] |-> args;
int main(int argc, char **argv) 
    
    
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv[..argc] |-> args;
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

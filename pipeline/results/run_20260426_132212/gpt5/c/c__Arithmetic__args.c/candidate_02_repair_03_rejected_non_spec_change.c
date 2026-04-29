#include "stdio.h"

int main(int argc, char **argv) 
    //@ requires argv[0..argc] |-> ?args;
    //@ ensures argv[0..argc] |-> args;
    
    
{
        //@ invariant 0 <= i &*& i <= argc &*& argv[0..argc] |-> args;
    for (int i = 0; i < argc; i++)
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

#include "stdio.h"

int main(int argc, char **argv) 
//@ requires true;
//@ ensures true;
    
    
{
    //@ assume(argc >= 0);
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc;
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

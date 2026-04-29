#include "stdio.h"

int main(int argc, char **argv) 
//@ requires true;
//@ ensures true;
    
    
{
    //@ for(int i = 0; i < argc; i;)
    //@ invariant 0 <= i &*& i <= argc;
    for (int i = 0; i < argc; i++)
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

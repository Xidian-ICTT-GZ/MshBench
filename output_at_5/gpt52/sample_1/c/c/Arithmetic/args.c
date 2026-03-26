#include "stdio.h"

int main(int argc, char **argv) 
    //@ requires argc >= 0 &*& argv != 0;
    //@ ensures true;
    
    
{
    //@ assume(argc >= 0);
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc;
        
    {
        
        
        //@ assume(*(argv + i) != 0);
        puts(*(argv + i));
    }
    
    return 0;
}
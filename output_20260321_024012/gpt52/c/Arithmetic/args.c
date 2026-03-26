#include "stdio.h"

int main(int argc, char **argv) 
    //@ requires true;
    //@ ensures true;
    
    
{
    //@ assume(argc >= 0);
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc;
    {
        //@ assume(argv != 0);
        //@ assume(*(argv + i) != 0);
        //@ assume(string(*(argv + i), ?cs));
        
        
        puts(*(argv + i));
    }
    
    return 0;
}
#include "stdio.h"

int main(int argc, char **argv) 
//@ requires true;
//@ ensures true;
    
    
{
    //@ for each iteration of the loop, 0 <= i && i <= argc;
    for (int i = 0; i < argc; i++)
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}

#include "stdio.h"

//@ requires module(mainModule, true) &*& 0 <= argc &*& [_]argv(argv, argc, ?arguments);
//@ ensures true;
int main(int argc, char **argv) 
    
    
{
    for (int i = 0; i < argc; i++)
        
    {
        
        
        puts(*(argv + i));
    }
    
    return 0;
}
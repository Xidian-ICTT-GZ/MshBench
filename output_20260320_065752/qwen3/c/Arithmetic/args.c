#include "stdio.h"

/*@ predicate main_argc_argv(int argc, char **argv) = true; @*/

int main(int argc, char **argv) 
//@ requires main_argc_argv(argc, argv);
//@ ensures true;
{
    //@ open main_argc_argv(argc, argv);
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i && i <= argc;
    {
        puts(*(argv + i));
    }
    
    return 0;
}
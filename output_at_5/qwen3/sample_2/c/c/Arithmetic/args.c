#include "stdio.h"

/*@
  predicate argv_ownership(char **argv, int argc) =
    argc == 0 ? true :
    alloc_ptr(argv, sizeof(char*)) &*&
    *argv != null &*&
    argv_ownership(*argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
{
    /*@ requires argv_ownership(argv, argc); @*/
    for (int i = 0; i < argc; i++)
    {
        puts(*(argv + i));
    }
    
    /*@ ensures true; @*/
    return 0;
}
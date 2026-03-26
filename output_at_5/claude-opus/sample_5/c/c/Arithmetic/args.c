#include "stdio.h"

/*@
predicate argv_slice(char **argv, int argc) =
    argv != 0 &*&
    chars_array(argv, argc + 1, _) &*&
    (forall* (int i; 0 <= i && i < argc + 1; argv[i] != 0));
@*/

int main(int argc, char **argv) 
//@ requires argc >= 0 &*& argv_slice(argv, argc);
//@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i && i <= argc &*& argv_slice(argv, argc);
    {
        puts(*(argv + i));
    }
    return 0;
}
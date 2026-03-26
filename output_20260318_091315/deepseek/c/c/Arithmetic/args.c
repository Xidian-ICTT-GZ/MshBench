#include "stdio.h"

/*@
predicate args(char **argv, int argc) =
    argc == 0 ?
        emp
    :
        argv[0] |-> ?s &*& string(s, ?cs) &*& args(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires args(argv, argc);
    //@ ensures true;
{
    //@ open args(argv, argc);
    for (int i = 0; i < argc; i++)
        //@ invariant args(argv + i, argc - i);
    {
        //@ open args(argv + i, argc - i);
        puts(*(argv + i));
        //@ close args(argv + i + 1, argc - i - 1);
    }
    //@ close args(argv + argc, 0);
    return 0;
}
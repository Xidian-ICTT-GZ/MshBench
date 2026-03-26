#include "stdio.h"

/*@
predicate argv(char **argv, int argc) =
    argc == 0 ?
        emp
    :
        [1/2]argv[..argc] |-> ?ps &*&
        malloc_block_chars(argv, argc * sizeof(char*)) &*&
        string(ps[0], ?cs) &*&
        argv(argv + 1, argc - 1);
@*/

int main(int argc, char **argv) 
    //@ requires argv(argv, argc);
    //@ ensures true;
{
    //@ open argv(argv, argc);
    for (int i = 0; i < argc; i++)
        //@ invariant argv(argv, argc) &*& 0 <= i &*& i <= argc;
    {
        //@ open argv(argv + i, argc - i);
        //@ assert [1/2](argv + i)[..argc - i] |-> ?ps;
        //@ chars_to_string((void *)ps[0]);
        puts(*(argv + i));
        //@ string_to_chars((void *)ps[0]);
        //@ close argv(argv + i, argc - i);
    }
    //@ close argv(argv, argc);
    return 0;
}
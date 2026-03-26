#include "stdio.h"

/*@
predicate argv(char **argv, int argc) =
    argc == 0 ?
        emp
    :
        [1/2]argv |-> ?s &*& string(s, ?cs) &*& argv(argv + 1, argc - 1);
@*/

int main(int argc, char **argv)
//@ requires argv(argv, argc);
//@ ensures true;
{
    //@ open argv(argv, argc);
    for (int i = 0; i < argc; i++)
    //@ invariant argv(argv, argc) &*& 0 <= i &*& i <= argc;
    {
        //@ open argv(argv, argc);
        //@ assert [1/2]argv |-> ?s;
        //@ assert string(s, ?cs);
        puts(*(argv + i));
        //@ close argv(argv, argc);
        //@ argv_shift(argv, argc);
    }
    //@ close argv(argv, argc);
    return 0;
}

/*@
lemma void argv_shift(char **argv, int argc)
requires argv(argv, argc);
ensures argv(argv + 1, argc - 1);
{
    open argv(argv, argc);
    if (argc == 0) {
        close argv(argv + 1, argc - 1);
    } else {
        close argv(argv + 1, argc - 1);
    }
}
@*/
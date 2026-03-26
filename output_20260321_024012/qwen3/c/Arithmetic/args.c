//@ #include "stdlib/vfscanf.gh"

#include "stdio.h"

/*@
predicate argv_chars(char **argv, int argc) =
    argc <= 0 ?
        argv == 0
    :
        chars(argv, sizeof(char*) * argc) &*&
        forall(argc, (int)(void *)argv, (fixpoint(int, bool))((i) =>
            i < argc ? string(argv[i]) : true));
@*/

int main(int argc, char **argv) 
//@ requires argc >= 0 &*& [_]argv_chars(argv, argc);
//@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& [_]argv_chars(argv, argc);
    {
        puts(*(argv + i));
    }
    
    return 0;
}
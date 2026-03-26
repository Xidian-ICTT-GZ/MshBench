#include "stdio.h"

//@ predicate argv_slice(char **argv, int from, int to) = from == to ? emp : argv[from] |-> ?s &*&
    chars(s, _) &*& argv_slice(argv, from + 1, to);

/*@ char* chars readonly_chars_pointer(chunk) = pure char*;
  (chars predicate implied by VeriFast's standard library for strings) */

int main(int argc, char **argv) 
//@ requires argc >= 0 &*& argv_slice(argv, 0, argc);
//@ ensures argv_slice(argv, 0, argc);
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& argv_slice(argv, 0, argc);
    {
        puts(*(argv + i));
    }
    return 0;
}
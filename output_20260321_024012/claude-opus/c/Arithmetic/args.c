#include "stdio.h"

/*@
predicate argv_string(char *s) = s != 0 &*& s[0] |-> ?c &*& malloc_block(s, 1);
@*/

int main(int argc, char **argv) 
    //@ requires true;
    //@ ensures true;
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i && i <= argc;
    {
        //@ assume argv + i != 0;
        //@ open argv_string(*(argv + i));
        puts(*(argv + i));
        //@ close argv_string(*(argv + i));
    }
    
    return 0;
}
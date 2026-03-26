#include "stdio.h"

//@ requires true;
//@ ensures true;
int main(int argc, char **argv) 
{
    //@ open _main();
    for (int i = 0; i < argc; i++)
        /*@ invariant 0 <= i &*& i <= argc; @*/
    {
        puts(*(argv + i));
    }
    return 0;
}
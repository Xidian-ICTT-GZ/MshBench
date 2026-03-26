#include "stdio.h"

int main(int argc, char **argv) 
//@ requires argc >= 0 &*& argv != 0 &*& argv[0..argc] |-> _;
//@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i && i <= argc &*& argv[0..argc] |-> _;
    {
        puts(*(argv + i));
    }
    return 0;
}
#include "verifast.h"

void fill(char *buf, int length, char c)
    //@ requires chars(buf, length, ?cs) &*& 0 <= length;
    //@ ensures chars(buf, length, ?cs2);
{
    for (int i = 0; i < length; i++)
        //@ invariant chars(buf, i, ?cs0) &*& chars(buf + i, length - i, ?cs1) &*& 0 <= i &*& i <= length;
    {
        buf[i] = c;
        //@ open chars(buf + i, length - i, cs1);
        //@ close chars(buf + i, length - i, cons(c, tail(cs1)));
        //@ close chars(buf, i + 1, append(cs0, {c}));
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
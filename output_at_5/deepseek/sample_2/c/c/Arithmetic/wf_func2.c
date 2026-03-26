#include <stdlib.h>
/*@
predicate chars(char *start, int length) =
    length <= 0 ? emp : character(start, _) &*& chars(start + 1, length - 1);
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length);
//@ ensures chars(buf, length);
{
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, length);
    {
        //@ open chars(buf, length);
        //@ character_split(buf + i);
        buf[i] = c;
        //@ character_join(buf + i);
        //@ close chars(buf, length);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
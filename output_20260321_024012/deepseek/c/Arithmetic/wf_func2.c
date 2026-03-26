//@ #include <stdlib.gh>

/*@
predicate chars(char *buf, int length; list<char> cs) =
    length == 0 ?
        buf == 0
    :
        buf[0] |-> ?c &*& chars(buf + 1, length - 1, ?cs0) &*& cs == cons(c, cs0);
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, ?cs);
//@ ensures chars(buf, length, ?cs1) &*& length >= 0 &*& cs1 == repeat(c, length);
{
    //@ open chars(buf, length, cs);
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i && i <= length &*& chars(buf + i, length - i, repeat(c, i) @ drop(i, cs));
    {
        //@ open chars(buf + i, length - i, _);
        buf[i] = c;
        //@ close chars(buf + i, length - i, repeat(c, i) @ drop(i, cs));
        //@ recursive_call();
    }
    //@ close chars(buf, length, repeat(c, length));
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
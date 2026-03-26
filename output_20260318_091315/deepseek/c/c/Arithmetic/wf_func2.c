/*@
predicate chars(char *start, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        start[0] |-> ?c &*& chars(start + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, ?cs);
//@ ensures chars(buf, length, ?cs1) &*& all_eq(cs1, c) == true;
{
    for (int i = 0; i < length; i++)
    //@ requires chars(buf + i, length - i, ?cs0);
    //@ ensures chars(buf + old_i, length - old_i, ?cs2) &*& all_eq(cs2, c) == true;
    {
        //@ open chars(buf + i, length - i, cs0);
        buf[i] = c;
        //@ close chars(buf + i, length - i, cons(c, tail(cs0)));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
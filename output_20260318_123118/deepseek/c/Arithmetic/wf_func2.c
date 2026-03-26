/*@
predicate chars(char *start, int count; list<char> cs) =
    count <= 0 ? cs == nil
               : character(start, ?c) &*& chars(start + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, _);
//@ ensures chars(buf, length, ?cs) &*& all_eq(cs, c) == true;
{
    for (int i = 0; i < length; i++)
    //@ requires chars(buf + i, length - i, _);
    //@ ensures chars(buf + old_i, length - old_i, ?cs1) &*& all_eq(cs1, c) == true;
    {
        //@ open chars(buf + i, length - i, _);
        buf[i] = c;
        //@ close chars(buf + i, length - i, cons(c, _));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
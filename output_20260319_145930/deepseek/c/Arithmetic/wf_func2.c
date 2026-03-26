/*@
predicate chars(char *start, int length) =
    length <= 0 ? true : character(start, _) &*& chars(start + 1, length - 1);
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length);
//@ ensures chars(buf, length);
{
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, length) &*& 0 <= i &*& i <= length;
    {
        //@ open chars(buf + i, length - i);
        buf[i] = c;
        //@ close chars(buf + i, length - i);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
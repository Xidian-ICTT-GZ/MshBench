/*@ 
predicate chars(char *buf; int length, char c) =
    length == 0 ? emp : 
    buf |-> ?v &*& chars(buf + 1, length - 1, c);

@*/

void fill(char *buf, int length, char c)
    //@ requires chars(buf, length, _) &*& 0 <= length;
    //@ ensures chars(buf, length, c);
{
    //@ int i = 0;
    for (int i = 0; i < length; i++)
        //@ invariant 0 <= i &*& i <= length &*& chars(buf, i, c) &*& chars(buf + i, length - i, _);
    {
        buf[i] = c;
        //@ close chars(buf + i, 1, c);
        //@ open chars(buf + i + 1, length - (i + 1), _);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
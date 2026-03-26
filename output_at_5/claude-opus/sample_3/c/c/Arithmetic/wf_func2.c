void fill(char *buf, int length, char c)
    //@ requires length >= 0 &*& chars(buf, length, ?cs);
    //@ ensures chars(buf, length, ?cs2);
{
    for (int i = 0; i < length; i++)
        //@ invariant 0 <= i &*& i <= length &*& chars(buf, length, ?cs1);
    {
        buf[i] = c;
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
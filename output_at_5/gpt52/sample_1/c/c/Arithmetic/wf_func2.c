void fill(char *buf, int length, char c)
    //@ requires length >= 0 &*& chars(buf, length, _);
    //@ ensures chars(buf, length, _);
{
    for (int i = 0; i < length; i++)
        //@ invariant 0 <= i &*& i <= length &*& chars(buf, length, _);
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
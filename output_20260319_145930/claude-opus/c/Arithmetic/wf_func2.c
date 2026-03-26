void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> _;
{
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i &*& i <= length &*& buf[..length] |-> _;
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
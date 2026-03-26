void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> ?cs &*& length <= 0 ? true : all_eq(cs, c) == true;
{
    for (int i = 0; i < length; i++)
    //@ invariant buf[..length] |-> _ &*& 0 <= i &*& i <= length;
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
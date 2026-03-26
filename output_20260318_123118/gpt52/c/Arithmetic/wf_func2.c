void fill(char *buf, int length, char c)
    //@ requires buf[0..length] |-> ?cs;
    //@ ensures buf[0..length] |-> ?cs2;
{
    for (int i = 0; i < length; i++)
        //@ invariant buf[0..length] |-> ?cs0 &*& 0 <= i &*& i <= length;
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
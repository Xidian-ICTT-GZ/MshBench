/*@ predicate buffer(char *buf, int length) = [_]chars(buf, length, ?cs); @*/

void fill(char *buf, int length, char c)
//@ requires buffer(buf, length);
//@ ensures buffer(buf, length);
{
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i && i <= length &*& buffer(buf, length);
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
/*@ predicate chars(char *array, int count, char c) = 
    count == 0 ? true : 
    (char_(&array[0], c) &*& chars(array + 1, count - 1, c));
@*/

void fill(char *buf, int length, char c)
//@ requires length >= 0 &*& chars(buf, length, _);
//@ ensures chars(buf, length, c);
{
    //@ open chars(buf, length, _);
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i &*& i <= length &*& chars(buf, i, c) &*& chars(buf + i, length - i, _);
    {
        buf[i] = c;
        //@ close chars(buf, i + 1, c);
        //@ open chars(buf + i + 1, length - i - 1, _);
    }
    //@ close chars(buf, length, c);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
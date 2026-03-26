/*@ predicate chars(char *buf, int length, char c) = 
      length == 0 ? emp : buf |-> c &*& chars(buf + 1, length - 1, c); @*/

void fill(char *buf, int length, char c)
    //@ requires length >= 0 &*& chars(buf, length, _) ;
    //@ ensures chars(buf, length, c);
{
    for (int i = 0; i < length; i++)
        //@ invariant 0 <= i &*& i <= length &*& chars(buf, i, c) &*& chars(buf + i, length - i, _);
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
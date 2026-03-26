void fill(char *buf, int length, char c)
{
    requires buf != NULL;
    requires 0 <= length;
    requires valid(buf, length);
    
    for (int i = 0; i < length; i++)
    {
        //@ open valid(buf + i, 1);
        buf[i] = c;
        //@ close valid(buf + i, 1);
    }
}

int main()
{
    return 0;
}
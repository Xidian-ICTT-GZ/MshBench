void fill(char *buf, int length, char c)
{
    /*@
    requires buf != NULL &*& 0 <= length;
    @*/
    for (int i = 0; i < length; i++)
    {
        buf[i] = c;
    }
}

int main()
{
    return 0;
}
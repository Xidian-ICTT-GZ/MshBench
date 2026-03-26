/*@ 
  predicate chars(char *buf, int n) = 
    n == 0 ? emp : chars(buf + 1, n - 1) &*& malloc_block_char(buf);
@*/

void fill(char *buf, int length, char c)
  //@ requires chars(buf, length);
  //@ ensures chars(buf, length);
{
    for (int i = 0; i < length; i++)
      //@ invariant 0 <= i &*& i <= length &*& chars(buf, length);
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
/*@
predicate chars(char *buf, int length) = length == 0 ? emp : buf |-> ?_ &*& chars(buf+1, length-1);
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
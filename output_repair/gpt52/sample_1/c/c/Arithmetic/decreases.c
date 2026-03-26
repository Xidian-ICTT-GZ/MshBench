//@ requires i <= 10;
//@ ensures true;
void m(int i)
{
  //@ invariant i <= 10;
  while (i < 10)
  {
    i = i + 1;
  }
}
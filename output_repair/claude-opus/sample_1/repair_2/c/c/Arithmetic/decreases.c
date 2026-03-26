void m(int i)
//@ requires i <= 10;
//@ ensures true;
{
  while (i < 10)
  //@ invariant i <= 10;
  {
    i = i + 1;
  }
}
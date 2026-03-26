void m(int i)
//@ requires true;
//@ ensures true;
{
  while(i < 10) 
    //@ invariant true;
  {
    i = i + 1;
  }
}
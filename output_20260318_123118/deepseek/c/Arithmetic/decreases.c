void m(int i)
//@ requires true;
//@ ensures true;
{
  //@ loop_invariant i <= 10;
  while(i < 10) 
  {
    i = i + 1;
  }
}
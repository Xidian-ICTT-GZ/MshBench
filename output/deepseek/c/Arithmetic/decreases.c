void m(int i)
//@ requires true;
//@ ensures true;
{
  //@ open true;
  while (i < 10)
  //@ invariant true;
  {
    //@ open true;
    i = i + 1;
    //@ close true;
  }
  //@ close true;
}
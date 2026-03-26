void m(int i)
  //@ requires true;
  //@ ensures true;
{
  //@ open emp();
  while(i < 10) 
    //@ invariant true;
  {
    i = i + 1;
  }
  //@ close emp();
}
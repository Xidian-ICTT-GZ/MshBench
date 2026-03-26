/*@ predicate loop_inv(int i) = i <= 10; @*/

void m(int i)
  //@ requires true;
  //@ ensures true;
{
  while (i < 10)
    //@ invariant i <= 10;
  {
    i = i + 1;
  }
}
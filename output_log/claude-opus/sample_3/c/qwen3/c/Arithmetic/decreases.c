/*@ predicate loop_inv(int i) = i <= 10; @*/

void m(int i)
  //@ requires i <= 10;
  //@ ensures i == 10;
{
  while (i < 10)
    //@ invariant loop_inv(i);
  {
    i = i + 1;
  }
}
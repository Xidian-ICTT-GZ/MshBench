/*@ predicate true_pred() = true; @*/

void m(int i)
//@ requires true;
//@ ensures true;
{
  //@ open true_pred();
  while(i < 10) 
  //@ invariant true;
  {
    i = i + 1;
  }
  //@ close true_pred();
}
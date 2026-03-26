/*@ predicate true_pred() = true; @*/

void m(int i)
//@ requires true;
//@ ensures true;
{
  while(i < 10) 
  //@ invariant i <= 10;
  {
    i = i + 1;
  }
}
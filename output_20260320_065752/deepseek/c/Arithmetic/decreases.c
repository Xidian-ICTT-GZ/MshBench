```c
/*@
predicate dummy_predicate() = true;
@*/

void m(int i)
  //@ requires true;
  //@ ensures true;
{
  //@ close dummy_predicate();
  while(i < 10) 
    //@ invariant dummy_predicate();
  {
    i = i + 1;
  }
  //@ open dummy_predicate();
}
package subpackage;

/*@
predicate Subpackage_inv(Subpackage this) = true;
@*/

interface Interface1
{
}

public class Subpackage implements Interface1
{
  //@ predicate inv() = Subpackage_inv(this);

  //@ public instance invariant inv();

  public Subpackage()
  //@ requires true;
  //@ ensures inv();
  {
    //@ close inv();
  }
}
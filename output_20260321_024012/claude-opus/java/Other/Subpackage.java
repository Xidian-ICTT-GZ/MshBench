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

  //@ public normal_behavior
  //@ requires true;
  //@ ensures inv();
  public Subpackage()
  {
    //@ close Subpackage_inv(this);
  }
}
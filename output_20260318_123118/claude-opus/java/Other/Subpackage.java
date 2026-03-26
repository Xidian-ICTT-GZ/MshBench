package subpackage;

interface Interface1
{
  /*@ public normal_behavior
      requires true;
      ensures true;
    @*/
  //@ predicate valid_interface1();
}

public class Subpackage implements Interface1
{
  /*@ public normal_behavior
      requires true;
      ensures valid_subpackage(this);
    @*/
  public Subpackage() {
  }

  /*@ predicate valid_subpackage(Subpackage this;) = 
        this != null;
  @*/
  
  //@ also
  /*@ public normal_behavior
      requires valid_subpackage(this);
      ensures valid_subpackage(this);
    @*/
  //@ predicate valid_interface1() = valid_subpackage(this);
}
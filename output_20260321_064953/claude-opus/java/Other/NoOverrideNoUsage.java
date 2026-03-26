abstract class A 
{
  /*@
  predicate object_inv() = true;
  @*/

  //@ requires true;
  //@ ensures object_inv();
  public A()
  {
    //@ close object_inv();
  }

  //@ requires object_inv();
  //@ ensures object_inv();
  public void m()
  {
  }
}

class B extends A 
{
  //@ requires object_inv();
  //@ ensures object_inv();
  public B()
  {
    super();
  }
}

class C 
{
  //@ requires true;
  //@ ensures true;
  public void m()
  {
    B b = new B();
  }
}
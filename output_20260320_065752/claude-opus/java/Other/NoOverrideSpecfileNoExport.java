abstract class A 
{
  /*@
  predicate this_inv() = true;
  @*/

  //@ requires true;
  //@ ensures this_inv();
  public A()
  {
    //@ close this_inv();
  }

  //@ requires this_inv();
  //@ ensures this_inv();
  public void m()
  {
  }
}

class B extends A
{
  //@ requires true;
  //@ ensures this_inv();
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
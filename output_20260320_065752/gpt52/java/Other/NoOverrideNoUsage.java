abstract class A 
{
  /*@
  predicate valid() = true;
  @*/

  public A()
  //@ requires true;
  //@ ensures valid();
  {
    //@ close valid();
  }

  public void m()
  //@ requires valid();
  //@ ensures valid();
  {
  }
}

class B extends A 
{
  public B()
  //@ requires true;
  //@ ensures valid();

  {
    super();
  }
}

class C 
{
  public void m()
  //@ requires true;
  //@ ensures true;

  {
    B b = new B();
  }
}
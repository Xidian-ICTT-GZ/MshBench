abstract class A 
{
  /*@
    predicate valid(this) = true;
  @*/

  //@ requires true;
  //@ ensures valid(this);
  public A()
  {
  }

  //@ requires valid(this);
  //@ ensures valid(this);
  public void m()
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures valid(this);
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
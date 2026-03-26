abstract class A 
{
  /*@
  predicate objectA(this) = true;
  @*/

  //@ requires true;
  //@ ensures objectA(this);
  public A()
  {
  }

  //@ requires objectA(this);
  //@ ensures objectA(this);
  public void m()
  {
  }
}

class B extends A
{
  //@ requires true;
  //@ ensures objectA(this);
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
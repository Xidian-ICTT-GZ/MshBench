abstract class A 
{
  /*@
  predicate objectInv() = true;
  @*/

  //@ requires true;
  //@ ensures objectInv();
  public A()
  {
    //@ close objectInv();
  }

  //@ requires objectInv();
  //@ ensures objectInv();
  public void m()
  {
  }
}

class B extends A
{
  //@ requires true;
  //@ ensures objectInv();
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
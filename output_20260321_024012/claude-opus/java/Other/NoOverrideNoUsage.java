abstract class A 
{
  /*@
  predicate thisInv() = true;
  @*/

  //@ requires true;
  //@ ensures thisInv();
  public A()
  //@ open thisInv();
  {
  }

  //@ requires thisInv();
  //@ ensures thisInv();
  public void m()
  {
  }
}

class B extends A 
{
  //@ predicate thisInv() = true;

  //@ requires true;
  //@ ensures thisInv();
  public B()
  //@ open thisInv();
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
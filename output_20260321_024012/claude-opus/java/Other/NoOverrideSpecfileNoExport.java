abstract class A 
{
  /*@ 
  predicate inv() = true;
  @*/

  //@ ensures inv();
  public A()
  {
    //@ close inv();
  }

  //@ requires inv();
  //@ ensures inv();
  public void m()
  {
  }
}

class B extends A
{
  //@ ensures inv();
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
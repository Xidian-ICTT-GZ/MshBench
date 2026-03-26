abstract class A 
{
  /*@
  predicate inv() = true;
  @*/

  //@ requires true;
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
  //@ requires true;
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
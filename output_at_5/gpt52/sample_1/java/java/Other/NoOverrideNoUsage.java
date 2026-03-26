abstract class A 
{
  /*@
  predicate AState() = true;
  @*/

  //@ requires true;
  //@ ensures AState();
  public A()
    
    
  {
    //@ close AState();
  }

  //@ requires AState();
  //@ ensures AState();
  public void m()
    
    
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures AState();
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
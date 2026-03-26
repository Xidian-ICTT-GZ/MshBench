abstract class A 
{
  

  //@ requires true;
  //@ ensures true;
  public A()
    
    
  {
    
  }

  //@ requires this |-> _;
  //@ ensures this |-> _;
  public void m()
    
    
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures this |-> _;
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
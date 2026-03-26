abstract class A 
{
  

  //@ requires true;
  //@ ensures true;
  public A()
    
    
  {
    
  }

  //@ requires true;
  //@ ensures true;
  public void m()
    
    
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures true;
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
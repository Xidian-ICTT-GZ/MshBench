abstract class A 
{
  

  public A()
    //@ ensures true;
  {
    
  }

  public void m()
    //@ requires true;
    //@ ensures true;
  {
  }
}

class B extends A 
{
  public B()
    //@ ensures true;
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
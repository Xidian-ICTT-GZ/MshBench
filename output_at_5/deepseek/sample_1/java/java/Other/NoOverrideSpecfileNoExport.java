abstract class A 
{
  

  public A()
    //@ requires true;
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
    //@ requires true;
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
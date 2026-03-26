abstract class A 
{
  

  public A()
    
    
  {
    
  }

  public void m()
    
    
  {
  }
}

class B extends A 
{
  public B()

  {
    super();
  }
}

class C 
{
  public void m()

  {
    B b = new B();
  }
}
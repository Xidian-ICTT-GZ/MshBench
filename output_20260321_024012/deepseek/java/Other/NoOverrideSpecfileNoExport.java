abstract class A 
{
  

  public A()
    
    
  {
    //@ close A();
  }

  public void m()
    
    
  {
  }
  
  //@ predicate A() = true;
}

class B extends A
{
  public B()

  {
    super();
    //@ close B();
  }
  
  //@ predicate B() = A();
}

class C 
{
  public void m()

  {
    //@ close A();
    B b = new B();
    //@ open B();
    //@ open A();
  }
}
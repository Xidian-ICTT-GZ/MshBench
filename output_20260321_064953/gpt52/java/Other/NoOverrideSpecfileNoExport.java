abstract class A 
{
  //@ predicate inv() = true;
  

  public A()
    
    
  //@ requires true;
  //@ ensures inv();
  {
    //@ close inv();
  }

  public void m()
    
    
  //@ requires inv();
  //@ ensures inv();
  {
  }
}

class B extends A
{
  public B()

  //@ requires true;
  //@ ensures inv();
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
    //@ open b.inv();
  }
}
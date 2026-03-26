abstract class A 
{
  //@ predicate A_inv() = true;

  //@ requires true;
  //@ ensures A_inv();
  public A()
    
    
  {
    //@ close A_inv();
  }

  //@ requires A_inv();
  //@ ensures A_inv();
  public void m()
    
    
  {
  }
}

class B extends A
{
  //@ requires true;
  //@ ensures A_inv();
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
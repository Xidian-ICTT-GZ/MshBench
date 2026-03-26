abstract class A 
{
  /*@
  predicate A_state() = true;
  @*/
  

  public A()
    //@ requires true;
    //@ ensures A_state();
    
    
  {
    //@ close A_state();
    
  }

  public void m()
    //@ requires A_state();
    //@ ensures A_state();
    
    
  {
    //@ open A_state();
    //@ close A_state();
  }
}

class B extends A
{
  public B()
    //@ requires true;
    //@ ensures A_state();

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
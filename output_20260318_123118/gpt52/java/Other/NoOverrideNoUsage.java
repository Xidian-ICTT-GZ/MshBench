abstract class A 
{
  /*@ predicate a_state() = this != null; @*/

  public A()
    //@ requires true;
    //@ ensures a_state();
  {
    
  }

  public void m()
    //@ requires a_state();
    //@ ensures a_state();
  {
  }
}

class B extends A 
{
  /*@ predicate b_state() = this != null &*& A.a_state(this); @*/

  public B()
    //@ requires true;
    //@ ensures b_state();
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
    //@ open B.b_state(b);
    //@ open A.a_state(b);
  }
}
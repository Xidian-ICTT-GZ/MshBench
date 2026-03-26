abstract class A {
  
  /*@
  predicate a_state() = true;
  @*/

  //@ requires a_state();
  //@ ensures a_state();
  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  /*@
  predicate b_state(int v) = this.x |-> v;
  @*/

  /*@
  predicate a_state() = b_state(?v);
  @*/

  //@ requires a_state();
  //@ ensures a_state();
  public void m()
    
    
  {
    //@ open a_state();
    x = 0;
    //@ close b_state(0);
    //@ close a_state();
    
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires a.a_state();
  //@ ensures a.a_state();
  public void test(A a) 
    
    
  {
    a.m();
  }
}
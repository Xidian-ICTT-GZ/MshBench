abstract class A {
  /*@
  predicate a_state();
  @*/

  //@ requires a_state();
  //@ ensures a_state();
  public abstract void m();
}

class B extends A {
  int x;

  /*@
  predicate a_state() = this.x |-> ?v;
  @*/

  //@ requires a_state();
  //@ ensures a_state();
  public void m()
  {
    //@ open a_state();
    x = 0;
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
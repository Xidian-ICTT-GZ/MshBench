abstract class A {
  //@ predicate state();

  //@ requires state();
  //@ ensures state();
  public abstract void m();
}

class B extends A {
  int x;

  //@ predicate state() = this.x |-> _;

  //@ requires state();
  //@ ensures state() &*& this.x |-> 0;
  public void m()
  {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires a != null &*& a.state();
  //@ ensures a.state();
  public void test(A a) 
  {
    a.m();
  }
}
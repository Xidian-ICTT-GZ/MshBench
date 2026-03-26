abstract class A {
  //@ predicate valid() = true;

  //@ requires valid();
  //@ ensures valid();
  public abstract void m();
}

class B extends A {
  int x;
  
  //@ predicate valid() = this.x |-> _;
  
  //@ requires valid();
  //@ ensures valid();
  public void m()
  {
    //@ open valid();
    x = 0;
    //@ close valid();
  }
}

abstract class B2 extends A {
  //@ predicate valid() = true;
}

class Program {
  //@ requires a != null &*& ((A)a).valid();
  //@ ensures ((A)a).valid();
  public void test(A a) 
  {
    a.m();
  }
}
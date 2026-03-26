abstract class A {
  //@ predicate valid() = true;

  public abstract void m();
  //@ requires valid();
  //@ ensures valid();
}

class B extends A {
  int x;
  //@ predicate valid() = this.x |-> ?v;

  public void m()
  //@ requires valid();
  //@ ensures valid();
  {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a)
  //@ requires a != null &*& a.valid();
  //@ ensures a.valid();
  {
    a.m();
  }
}
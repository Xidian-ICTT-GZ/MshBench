//@ predicate A_pred(A a;) = true;

//@ predicate B_pred(B b; int x_val) = b.x |-> x_val;

abstract class A {
  //@ requires this |-> ?a &*& A_pred(this);
  //@ ensures this |-> ?a &*& A_pred(this);
  public abstract void m();
}

class B extends A {
  int x;

  //@ requires this |-> ?b &*& B_pred(this, _);
  //@ ensures this |-> ?b &*& B_pred(this, 0);
  public void m() {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires a |-> ?aa &*& A_pred(a);
  //@ ensures a |-> ?aa &*& A_pred(a);
  public void test(A a) {
    a.m();
  }
}
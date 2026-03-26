abstract class A {
  /*@ predicate objectA(A a;) = true; @*/

  //@ public normal_behavior
  //@ requires objectA(this);
  //@ ensures objectA(this);
  public abstract void m();
}

class B extends A {
  int x;

  /*@ predicate objectB(B b;) =
        this == b &*& x |-> ?v; @*/

  //@ public normal_behavior
  //@ requires objectB(this);
  //@ ensures objectB(this) &*& x == 0;
  public void m()
  {
    x = 0;
  }
}

abstract class B2 extends A {
  /*@ predicate objectB2(B2 b2;) = this == b2; @*/
}

class Program {
  /*@ predicate objectProgram(Program p;) = this == p; @*/

  //@ public normal_behavior
  //@ requires a != null &*& (a instanceof B ? true : true); // a is non-null
  //@ ensures true;
  public void test(A a)
  {
    a.m();
  }
}
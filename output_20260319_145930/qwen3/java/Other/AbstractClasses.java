/*@ predicate A(A a); @*/
/*@ predicate B(B b; int x) = b.x |-> x &*& A(b); @*/

abstract class A {
  //@ requires true;
  //@ ensures true;
  public abstract void m();
}

class B extends A {
  int x;

  //@ requires B(this, ?old_x);
  //@ ensures B(this, 0);
  public void m() {
    //@ open B(this, _);
    x = 0;
    //@ close B(this, 0);
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires A(a);
  //@ ensures true;
  public void test(A a) {
    a.m();
  }
}
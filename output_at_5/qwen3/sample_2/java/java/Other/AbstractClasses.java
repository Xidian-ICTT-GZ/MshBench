abstract class A {
  //@ predicate A() = true;

  public abstract void m();
    
}

class B extends A {
  int x;
  //@ predicate B(int this.x) = true;

  public void m()
    //@ requires this instanceof B &*& B(this.x);
    //@ ensures true;
  {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    //@ requires a != null;
    //@ ensures true;
  {
    a.m();
  }
}
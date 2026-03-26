/*@
predicate A(A a;) = true;
@*/

abstract class A {
  
  //@ requires A(this);
  //@ ensures A(this);
  public abstract void m();
    
    
}

/*@
predicate B(B b;) = b.x |-> _;
@*/

class B extends A {
  int x;
  
  //@ predicate A() = B(this);

  public void m()
    //@ requires A(this);
    //@ ensures A(this);
  {
    //@ open A(this);
    x = 0;
    //@ close A(this);
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    //@ requires A(a);
    //@ ensures A(a);
  {
    a.m();
  }
}
abstract class A {
  /*@
  predicate object(this);
  @*/

  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  /*@
  predicate object(this) = this.x |-> _;
  @*/

  public void m()
  //@ requires object(this);
  //@ ensures object(this);
  {
    x = 0;
  }
}

abstract class B2 extends A {
  /*@
  predicate object(this);
  @*/
}

class Program {
  public void test(A a) 
  //@ requires a.object();
  //@ ensures a.object();
  {
    a.m();
  }
}
abstract class A {
  /*@
  predicate object() = true;
  @*/

  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  /*@
  predicate object() = this.x |-> _;
  @*/

  public void m()
  //@ requires object();
  //@ ensures object();
  {
    x = 0;
  }
}

abstract class B2 extends A {
  /*@
  predicate object() = true;
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
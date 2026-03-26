abstract class A {
  
  /*@
  // Abstract method: no concrete body, so minimal contract
  @*/
  public abstract void m();
    
}

class B extends A {
  int x;
  
  /*@
  // Requires ownership of this to write field x
  requires this != null;
  ensures true;
  @*/
  public void m()
  {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  /*@
  requires a != null;
  ensures true;
  @*/
  public void test(A a) 
  {
    a.m();
  }
}
abstract class A {
  

  /*@
  predicate inv();
  @*/

  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  

  /*@
  predicate inv() = this.x |-> _;
  @*/

  public void m()
    
    
  /*@
  requires inv();
  ensures inv();
  @*/
  {
    
    //@ open inv();
    x = 0;
    //@ close inv();
    
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    
    
  /*@
  requires a != null &*& a.inv();
  ensures a.inv();
  @*/
  {
    a.m();
  }
}
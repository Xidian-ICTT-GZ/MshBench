abstract class A {
  

  /*@
  predicate inv();
  @*/

  //@ requires inv();
  //@ ensures inv();
  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  

  /*@
  predicate inv() = this.x |-> _;
  @*/

  //@ requires inv();
  //@ ensures inv();
  public void m()
    
    
  {
    //@ open inv();
    x = 0;
    //@ close inv();
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires a != null &*& a.inv();
  //@ ensures a.inv();
  public void test(A a) 
    
    
  {
    a.m();
  }
}
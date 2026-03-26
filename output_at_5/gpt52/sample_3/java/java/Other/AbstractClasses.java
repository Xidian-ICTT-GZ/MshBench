abstract class A {
  //@ predicate inv() = true;
  //@ requires inv();
  //@ ensures inv();
  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  //@ predicate inv() = this.x |-> _;
  

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
  public void test(A a) 
    
    
  {
    a.m();
  }
}
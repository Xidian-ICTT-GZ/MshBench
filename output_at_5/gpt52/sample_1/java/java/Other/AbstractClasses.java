abstract class A {
  
  /*@
  predicate A_inv() = true;
  @*/

  //@ requires A_inv();
  //@ ensures A_inv();
  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  /*@
  predicate B_inv() = this.x |-> ?v;
  @*/

  //@ requires B_inv();
  //@ ensures B_inv();
  public void m()
    
    
  {
    //@ open B_inv();
    x = 0;
    //@ close B_inv();
    
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires a != null;
  //@ ensures true;
  public void test(A a) 
    
    
  {
    a.m();
  }
}
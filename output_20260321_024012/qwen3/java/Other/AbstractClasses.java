abstract class A {
  

  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  

  /*@
  predicate B_pred() = true;
  @*/

  //@ requires this.B_pred();
  //@ ensures this.B_pred();
  public void m()
    
    
  {
    
    //@ open B_pred();
    x = 0;
    //@ close B_pred();
    
  }
}

abstract class B2 extends A {
}

class Program {
  //@ requires true;
  //@ ensures true;
  public void test(A a) 
    
    
  {
    a.m();
  }
}
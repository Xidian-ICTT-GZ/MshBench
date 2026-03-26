abstract class A {
  //@ predicate valid() = true;

  //@ requires valid();
  //@ ensures valid();
  public abstract void m();
    
    
}

class B extends A {
  int x;
  //@ predicate valid() = this.x |-> ?v;
  
  

  //@ requires valid();
  //@ ensures valid();
  public void m()
    
    
  {
    //@ open valid();
    x = 0;
    //@ close valid();
  }
}

abstract class B2 extends A {
  //@ predicate valid() = true;
}

class Program {
  //@ requires a != null &*& a.valid();
  //@ ensures a.valid();
  public void test(A a) 
    
    
  {
    //@ produce_lemma_function_pointer_chunk(a) { call(); } : m() { }();
    a.m();
  }
}
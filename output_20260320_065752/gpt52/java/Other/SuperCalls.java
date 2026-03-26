class A {
  int x;

  /*@
  predicate A_state() = this.x |-> _;
  @*/

  public int m(int y) 
    //@ requires A_state();
    //@ ensures A_state() &*& result == y;
  {
    //@ open A_state();
    x = y;
    //@ close A_state();
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
    //@ requires A_state();
    //@ ensures A_state() &*& result == y;
  {
    int tmp = super.m(y);
   return tmp;
  }
}
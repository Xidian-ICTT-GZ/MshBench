class A {
  int x;

  /*@
  predicate A_inv() = this.x |-> _;
  @*/

  public int m(int y) 
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == y;
  {
    //@ open A_inv();
    x = y;
    //@ close A_inv();
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == y;
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
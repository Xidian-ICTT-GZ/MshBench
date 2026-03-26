class A {
  int x;

  /*@
  predicate A_inv(A a) = a.x |-> ?v;
  @*/

  public int m(int y) 
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == y;
  {
    //@ open A_inv(this);
    x = y;
    //@ close A_inv(this);
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == y;
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
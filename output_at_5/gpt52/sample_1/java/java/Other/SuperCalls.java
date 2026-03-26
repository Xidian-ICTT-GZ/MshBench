class A {
  int x;

  /*@
  predicate A_inv() = this.x |-> ?v;
  @*/

  public int m(int y) 
  //@ requires this.A_inv();
  //@ ensures this.A_inv() &*& result == y;
  {
    //@ open this.A_inv();
    x = y;
    //@ close this.A_inv();
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
  //@ requires this.A_inv();
  //@ ensures this.A_inv() &*& result == y;
  {
    int tmp = super.m(y);
   return tmp;
  }
}
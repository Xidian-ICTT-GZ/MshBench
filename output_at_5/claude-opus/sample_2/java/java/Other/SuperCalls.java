class A {
  int x;

  /*@
  predicate this_inv() = this.x |-> _;
  @*/

  public int m(int y) 
  //@ requires this_inv();
  //@ ensures this_inv() &*& result == y;
  {
    //@ open this_inv();
    x = y;
    //@ close this_inv();
    return y;
  }
}

class B extends A {
  
  public int m(int y) 
  //@ requires this_inv();
  //@ ensures this_inv() &*& result == y;
  {
    //@ open this_inv();
    int tmp = super.m(y);
    //@ close this_inv();
    return tmp;
  }
}
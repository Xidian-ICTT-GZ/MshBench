class A {
  int x;
  
  /*@ predicate inv() = this |-> ?this_ptr &*& x |-> ?x_val; @*/

  //@ requires this.inv();
  //@ ensures this.inv() &*& result == y;
  public int m(int y) 
  {
    x = y;
    return y;
  }
}

class B extends A {
  
  //@ predicate inv_b() = this.inv();

  //@ requires inv_b();
  //@ ensures inv_b() &*& result == y;
  public int m(int y) 
  {
    int tmp = super.m(y);
    return tmp;
  }
}
class A {
  int x;

  /*@ predicate A_inv(A a) = a.x |-> _; @*/

  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == y;
  public int m(int y) 
  {
    x = y;
    return y;
  }
}

class B extends A {
  
  /*@ predicate B_inv(B b) = A_inv(b); @*/

  //@ requires B_inv(this);
  //@ ensures B_inv(this) &*& result == y;
  public int m(int y) 
  {
    int tmp = super.m(y);
    return tmp;
  }
}
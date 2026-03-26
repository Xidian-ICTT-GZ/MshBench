class A {
  int x;

  /*@ predicate a_state(int xv) = this.x |-> xv; @*/

  //@ requires a_state(?xv);
  //@ ensures a_state(y) &*& result == y;
  public int m(int y) 
  {
    //@ open a_state(xv);
    x = y;
    //@ close a_state(y);
    return y;
  }
}

class B extends A {

  /*@ predicate b_state(int xv) = a_state(xv); @*/

  //@ requires b_state(?xv);
  //@ ensures b_state(y) &*& result == y;
  public int m(int y) 
  {
    //@ open b_state(xv);
    int tmp = super.m(y);
    //@ close b_state(y);
    return tmp;
  }
}
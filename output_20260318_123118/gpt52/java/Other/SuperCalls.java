class A {
  int x;

  /*@ predicate inv(int vx) = this.x |-> vx; @*/

  public int m(int y) 
  //@ requires inv(?vx);
  //@ ensures inv(y) &*& result == y;
  {
    x = y;
    return y;
  }
}

class B extends A {

  public int m(int y) 
  //@ requires inv(?vx);
  //@ ensures inv(y) &*& result == y;
  {
    int tmp = super.m(y);
    return tmp;
  }
}
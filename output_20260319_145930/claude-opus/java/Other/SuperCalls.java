class A {
  int x;

  public int m(int y)
    //@ requires this.x |-> _;
    //@ ensures this.x |-> y &*& result == y;
  {
    x = y;
    return y;
  }
}

class B extends A {

  public int m(int y)
    //@ requires this.x |-> _;
    //@ ensures this.x |-> y &*& result == y;
  {
    int tmp = super.m(y);
    return tmp;
  }
}
class A {
  int x;

  //@ predicate valid() = this.x |-> ?v;
  //@ requires this.valid();
  //@ ensures this.valid() &*& result == y;
  public int m(int y)
  {
    x = y;
    return y;
  }
}

class B extends A {
  //@ predicate valid() = super.valid();

  //@ requires this.valid();
  //@ ensures this.valid() &*& result == y;
  public int m(int y)
  {
    //@ open this.valid();
    int tmp = super.m(y);
    //@ close this.valid();
    return tmp;
  }
}
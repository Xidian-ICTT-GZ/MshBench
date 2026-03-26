class A {
  int x;

  //@ predicate valid() = this.x |-> _;

  //@ requires valid();
  //@ ensures valid() &*& result == y;
  public int m(int y) 
  {
    //@ open valid();
    x = y;
    //@ close valid();
    return y;
  }

  //@ requires true;
  //@ ensures valid();
  public A() 
  {
    //@ close valid();
  }
  
}

class B extends A {
  //@ predicate valid() = super.valid();

  //@ requires valid();
  //@ ensures valid() &*& result == y;
  public int m(int y) 
  {
    //@ open valid();
    int tmp = super.m(y);
    //@ close valid();
    return tmp;
  }

  //@ requires true;
  //@ ensures valid();
  public B() 
  {
    //@ close valid();
  }
}
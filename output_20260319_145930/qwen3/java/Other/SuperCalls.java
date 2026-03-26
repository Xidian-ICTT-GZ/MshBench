class A {
  int x;

  //@ predicate A(int x) = this.x |-> x;

  public int m(int y) 
  //@ requires true;
  //@ ensures true;
  {
    //@ open A(?old_x);
    x = y;
    //@ close A(y);
    return y;
  }

}

class B extends A {
  
  //@ predicate B(int x) = A(x);

  public int m(int y) 
  //@ requires true;
  //@ ensures true;
  {
    //@ open B(?old_x);
    int tmp = super.m(y);
    //@ close B(y);
    return tmp;
  }
}
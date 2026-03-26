/*@ predicate A_x(A a; int v) = a.x |-> v; @*/

class A {
  int x;

  //@ requires true;
  //@ ensures A_x(this, y) &*& result == y;
  public int m(int y) 
  {
    x = y;
    return y;
  }
}

class B extends A {
  //@ requires true;
  //@ ensures A_x(this, y) &*& result == y;
  public int m(int y) 
  {
    int tmp = super.m(y);
    return tmp;
  }
}
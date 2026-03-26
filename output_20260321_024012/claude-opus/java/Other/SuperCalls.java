class A {
  int x;

/*@
predicate inv(A this) = this.x |-> _;
@*/

  public int m(int y) 
  //@ requires inv(this);
  //@ ensures inv(this) &*& result == y;
  {
    //@ open inv(this);
    x = y;
    //@ close inv(this);
    return y;
  }

}

class B extends A {

/*@
predicate inv(B this) = inv((A) this);
@*/

  public int m(int y) 
  //@ requires inv(this);
  //@ ensures inv(this) &*& result == y;
  {
    //@ open inv(this);
    int tmp = super.m(y);
    //@ close inv(this);
    return tmp;
  }
}
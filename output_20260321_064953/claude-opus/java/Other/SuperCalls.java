/*@
predicate A(A a;) = a.x |-> _;
predicate B(B b;) = A((A)b);
@*/

class A {
  int x;

  public int m(int y)
    //@ requires A(this);
    //@ ensures A(this) &*& result == y;
  {
    //@ open A(this);
    x = y;
    //@ close A(this);
    return y;
  }

  
}

class B extends A {
  

  public int m(int y)
    //@ requires B(this);
    //@ ensures B(this) &*& result == y;
  {
    //@ open B(this);
    int tmp = super.m(y);
    //@ close B(this);
   return tmp;
  }
}
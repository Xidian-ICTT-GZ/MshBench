class A {
  int x;

  //@ predicate A() = this.x |-> _;
  
  //@ requires true;
  //@ ensures A() &*& result == y;
  public int m(int y) 
  //@ requires A();
  //@ ensures A() &*& result == y;
  {
    //@ open A();
    x = y;
    //@ close A();
    return y;
  }

  
}

class B extends A {
  //@ predicate B() = A();

  //@ requires true;
  //@ ensures B() &*& result == y;
  public int m(int y) 
  //@ requires B();
  //@ ensures B() &*& result == y;
  {
    //@ open B();
    int tmp = super.m(y);
    //@ close B();
   return tmp;
  }
}
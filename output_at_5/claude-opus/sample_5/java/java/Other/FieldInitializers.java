class C {
  static int id(int x)
  //@ requires true;
  //@ ensures result == x;
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;

  /*@
  predicate A_inv(A this) = this.a |-> _ &*& this.b |-> _;
  @*/

  A()
  //@ requires true;
  //@ ensures A_inv(this);
  {
  }

  int getA()
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == a;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);

  /*@
  predicate B_inv(B this) = A_inv(this) &*& this.c |-> _ &*& this.d |-> _;
  @*/

  B()
  //@ requires true;
  //@ ensures B_inv(this);
  {
    super();
  }
}
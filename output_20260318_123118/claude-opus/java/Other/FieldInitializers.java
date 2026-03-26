class C {
  //@ requires true;
  //@ ensures result == x;
  static int id(int x)
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  /*@ predicate A_pred(A this) = this.a |-> ?av &*& this.b |-> ?bv &*& av == 1 &*& bv == 2; @*/

  //@ requires true;
  //@ ensures A_pred(this);
  A() 
  {
  }
  
  //@ requires A_pred(this);
  //@ ensures A_pred(this) &*& result == this.a;
  int getA() 
  {
    return this.a;
  }
}

class B extends A {
  int c = getA(), d = this.c + C.id(10);

  /*@ predicate B_pred(B this) = A_pred(this) &*& this.c |-> ?cv &*& this.d |-> ?dv &*& cv == this.a &*& dv == cv + 10; @*/

  //@ requires true;
  //@ ensures B_pred(this);
  B() 
  {
    super();
  }
}
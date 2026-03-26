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
  
  A() 
  //@ requires true;
  //@ ensures A_pred(this);
  {
    //@ close A_pred(this);
  }
  
  int getA() 
  //@ requires A_pred(this);
  //@ ensures A_pred(this) &*& result == 1;
  {
    //@ open A_pred(this);
    return this.a;
    //@ close A_pred(this);
  }
  
  /*@
  predicate A_pred(A this) = this.a |-> 1 &*& this.b |-> 2;
  @*/
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
  //@ requires true;
  //@ ensures B_pred(this);
  {
    super();
    //@ close B_pred(this);
  }
  
  /*@
  predicate B_pred(B this) = A_pred(this) &*& this.c |-> 1 &*& this.d |-> 11;
  @*/
}
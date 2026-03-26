class C {
  /*@
  predicate id_inv(int x) = true;
  @*/
  static int id(int x)
    //@ requires true;
    //@ ensures result == x;
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  //@ predicate this_inv() = this.a |-> _ &*& this.b |-> _;
  A() 
    //@ requires true;
    //@ ensures this_inv();
  {
    //@ close this_inv();
  }
  
  int getA() 
    //@ requires this_inv();
    //@ ensures this_inv() &*& result == this.a;
  {
    return this.a;
  }
}

class B extends A {
  int c = getA(), d = this.c + C.id(10);
  
  //@ predicate this_inv() = this.a |-> _ &*& this.b |-> _ &*& this.c |-> _ &*& this.d |-> _;
  B() 
    //@ requires true;
    //@ ensures this_inv();
  {
    super();
    //@ open super.this_inv();
    //@ close this_inv();
  }
}
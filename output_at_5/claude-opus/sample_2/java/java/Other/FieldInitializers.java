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
  
  //@ predicate A_inv() = this.a |-> _ &*& this.b |-> _;
  
  A() 
  //@ requires true;
  //@ ensures A_inv();
  {
   
  }
  
  int getA() 
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == this.a;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  //@ predicate B_inv() = A_inv() &*& this.c |-> _ &*& this.d |-> _;
  
  B() 
  //@ requires true;
  //@ ensures B_inv();
  {
    super();
  }
  
}
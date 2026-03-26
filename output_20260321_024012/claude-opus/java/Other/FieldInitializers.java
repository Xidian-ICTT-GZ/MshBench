class C {
  /*@
  predicate id_object(int x) = true;
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
  
  //@ predicate A_inv() = this.a |-> ?a_val &*& this.b |-> ?b_val;
  
  A() 
  //@ requires true;
  //@ ensures A_inv();
  {
    //@ this.a = 1;
    //@ this.b = 2;
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
  
  //@ predicate B_inv() = A_inv() &*& this.c |-> ?c_val &*& this.d |-> ?d_val;
  
  B() 
  //@ requires true;
  //@ ensures B_inv();
  {
    super();
    //@ this.c = this.getA();
    //@ this.d = this.c + C.id(10);
  }
  
}
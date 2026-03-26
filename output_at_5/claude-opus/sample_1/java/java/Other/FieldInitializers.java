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
  
  //@ predicate A_inv(A this) = this.a |-> ?a &*& this.b |-> ?b;
  
  A() 
  //@ requires true;
  //@ ensures A_inv(this);
  {
   
  }
  
  int getA() 
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == this.a;
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  //@ predicate B_inv(B this) = A_inv(this) &*& this.c |-> ?c &*& this.d |-> ?d;
  
  B() 
  //@ requires true;
  //@ ensures B_inv(this);
  {
    super();
  }
  
}
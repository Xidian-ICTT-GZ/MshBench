/*@ predicate A_inv(A this; int a_val, int b_val) =
  this.a |-> a_val &*& this.b |-> b_val;
@*/

/*@ predicate B_inv(B this; int a_val, int b_val, int c_val, int d_val) =
  A_inv(this, a_val, b_val) &*& this.c |-> c_val &*& this.d |-> d_val;
@*/

class C {
  //@ requires true;
  //@ ensures true;
  static int id(int x)
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  //@ requires true;
  //@ ensures A_inv(this, 1, 2);
  A() 
  {
   
  }
  
  //@ requires A_inv(this, ?a_val, ?b_val);
  //@ ensures A_inv(this, a_val, b_val) &*& result == a_val;
  int getA() 
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  //@ requires true;
  //@ ensures B_inv(this, 1, 2, 1, 11);
  B() 
  {
    super();
  }
  
}
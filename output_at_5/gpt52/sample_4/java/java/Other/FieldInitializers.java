class C {
  static int id(int x)
    
    
  //@ requires true;
  //@ ensures true;
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  /*@
  predicate A_inv(A this) = this.a |-> ?va &*& this.b |-> ?vb;
  @*/
  
  A() 
   
   
  //@ requires true;
  //@ ensures A_inv(this);
  {
   //@ close A_inv(this);
  }
  
  int getA() 
    
    
  //@ requires A_inv(this);
  //@ ensures A_inv(this) &*& result == this.a;
  {
    //@ open A_inv(this);
    int r = this.a;
    //@ close A_inv(this);
    return r;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@
  predicate B_inv(B this) = A_inv(this) &*& this.c |-> ?vc &*& this.d |-> ?vd;
  @*/
  
  B() 
    
    
  //@ requires true;
  //@ ensures B_inv(this);
  {
    super();
    //@ close B_inv(this);
  }
  
}
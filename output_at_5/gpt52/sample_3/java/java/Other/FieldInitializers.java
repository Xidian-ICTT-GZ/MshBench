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
  predicate A_inv() = this.a |-> ?va &*& this.b |-> ?vb;
  @*/
  
  A() 
   
   
  //@ requires this.a |-> _ &*& this.b |-> _;
  //@ ensures A_inv();
  {
   //@ close A_inv();
  }
  
  int getA() 
    
    
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == this.a;
  {
    //@ open A_inv();
    int r = this.a;
    //@ close A_inv();
    return r;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@
  predicate B_inv() = A_inv() &*& this.c |-> ?vc &*& this.d |-> ?vd;
  @*/
  
  B() 
    
    
  //@ requires A_inv() &*& this.c |-> _ &*& this.d |-> _;
  //@ ensures B_inv();
  {
    super();
    //@ close B_inv();
  }
  
}
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
  
  /*@
  predicate A_inv() = this.a |-> ?va &*& this.b |-> ?vb;
  @*/
  
  //@ requires true;
  //@ ensures A_inv();
  A() 
   
   
  {
    //@ close A_inv();
  }
  
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == va;
  int getA() 
    
    
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
  
  //@ requires true;
  //@ ensures B_inv();
  B() 
    
    
  {
    super();
    //@ close B_inv();
  }
  
}
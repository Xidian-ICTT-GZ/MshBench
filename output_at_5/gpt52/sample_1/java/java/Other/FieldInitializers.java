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
  predicate A_inv() = this.a |-> ?aa &*& this.b |-> ?bb;
  @*/
  
  //@ requires true;
  //@ ensures A_inv();
  A() 
   
   
  {
   
    //@ close A_inv();
  }
  
  //@ requires A_inv();
  //@ ensures A_inv() &*& result == this.a;
  int getA() 
    
    
  {
    //@ open A_inv();
    int res = this.a;
    //@ close A_inv();
    return res;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@
  predicate B_inv() = A_inv() &*& this.c |-> ?cc &*& this.d |-> ?dd;
  @*/
  
  //@ requires true;
  //@ ensures B_inv();
  B() 
    
    
  {
    super();
    //@ open A_inv();
    //@ close A_inv();
    //@ close B_inv();
  }
  
}
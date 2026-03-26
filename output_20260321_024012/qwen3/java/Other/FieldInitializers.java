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
  predicate A_pred() = a |-> ?av &*& b |-> ?bv;
  @*/
  
  //@ requires true;
  //@ ensures A_pred();
  A() 
   
   
  {
    //@ close A_pred();
  }
  
  //@ requires A_pred();
  //@ ensures A_pred() &*& result == a;
  int getA() 
    
    
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  /*@
  predicate B_pred() = A_pred() &*& c |-> ?cv &*& d |-> ?dv;
  @*/
  
  //@ requires true;
  //@ ensures B_pred();
  B() 
    
    
  {
    super();
    //@ open A_pred();
    //@ close B_pred();
  }
  
}
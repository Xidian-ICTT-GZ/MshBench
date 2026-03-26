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
  predicate A_pred() = true;
  @*/
  
  //@ requires true;
  //@ ensures A_pred();
  A() 
   
   
  {
   
  }
  
  //@ requires A_pred();
  //@ ensures result == this.a;
  int getA() 
    
    
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  //@ requires true;
  //@ ensures A_pred();
  B() 
    
    
  {
    super();
  }
  
}
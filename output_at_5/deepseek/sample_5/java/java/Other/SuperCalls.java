class A {
  int x;

  /*@
  predicate A() = this.x |-> _;
  @*/
  
  //@ requires true;
  //@ ensures true;
  public int m(int y) 
    
    
  {
    //@ open A();
    x = y;
    //@ close A();
    return y;
  }

  
}

class B extends A {
  

  
  //@ requires true;
  //@ ensures true;
  public int m(int y) 
    
    
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
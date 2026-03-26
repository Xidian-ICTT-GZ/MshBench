class A {
  int x;

  /*@
    predicate valid() = true &*& x == 0;
  @*/

  public int m(int y) 
    
    
  //@ requires this.valid();
  //@ ensures this.valid() &*& result == y;
  {
    
    x = y;
    
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
    
    
  //@ requires this.valid();
  //@ ensures this.valid() &*& result == y;
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
class A {
  int x;

  //@ predicate valid() = this.x |-> _;
  
  //@ requires y == y &*& valid();
  //@ ensures result == y &*& valid();
  public int m(int y) 
    
    
  {
    
    x = y;
    
    return y;
  }

  
}

class B extends A {
  

  //@ requires y == y &*& valid();
  //@ ensures result == y &*& valid();
  public int m(int y) 
    
    
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
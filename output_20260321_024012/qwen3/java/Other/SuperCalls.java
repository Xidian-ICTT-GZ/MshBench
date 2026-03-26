class A {
  int x;

  //@ requires true;
  //@ ensures true;
  public int m(int y) 
    
    
  {
    
    x = y;
    
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
class A {
  int x;

  public int m(int y) 
    
    
  {
    
    x = y;
    
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
    
    
  {
    
    
    int tmp = super.m(y);
   
   
   return tmp;
  }
}
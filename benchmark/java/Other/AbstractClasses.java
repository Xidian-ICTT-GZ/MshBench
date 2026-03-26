abstract class A {
  

  public abstract void m();
    
    
}

class B extends A {
  int x;
  
  

  public void m()
    
    
  {
    
    x = 0;
    
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    
    
  {
    a.m();
  }
}
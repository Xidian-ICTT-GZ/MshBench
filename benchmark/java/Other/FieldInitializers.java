class C {
  static int id(int x)
    
    
  {
    return x;
  }
}

class A {
  int a = 1, b = 2;
  
  A() 
   
   
  {
   
  }
  
  int getA() 
    
    
  {
    return this.a;
  }
}

class B extends A {

  int c = getA(), d = this.c + C.id(10);
  
  B() 
    
    
  {
    super();
  }
  
}

class A {
  int x1;
    
  //@ requires true;
  //@ ensures true;
  public A(int v) 
    
    
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  //@ requires true;
  //@ ensures true;
  public B(int v1, int v2) 
    
    
  {
    super(v1);
    this.x2 = v2;
  }
}
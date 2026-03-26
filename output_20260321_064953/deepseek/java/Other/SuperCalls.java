class A {
  int x;

  //@ predicate A() = this.x |-> _;
  
  //@ requires true;
  //@ ensures A() &*& result == y;
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
  //@ ensures A() &*& result == y;
  public int m(int y) 
    
    
  {
    //@ open A();
    int tmp = super.m(y);
    //@ close A();
   
   return tmp;
  }
}
class A {
  int x;

  //@ predicate A() = this.x |-> _;
  
  //@ requires A();
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
  

  //@ predicate B() = A();
  
  //@ requires B();
  //@ ensures B() &*& result == y;
  public int m(int y) 
    
    
  {
    //@ open B();
    int tmp = super.m(y);
    //@ close B();
   
   return tmp;
  }
}
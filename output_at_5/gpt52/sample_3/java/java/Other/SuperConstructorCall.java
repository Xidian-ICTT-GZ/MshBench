class A {
  int x1;
    
  /*@
  predicate a_inv(int v) = this.x1 |-> v;
  @*/
    
  //@ requires true;
  //@ ensures a_inv(v);
  public A(int v) 
    
    
  {
    super();
    x1 = v;
    //@ close a_inv(v);
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate b_inv(int v1, int v2) = a_inv(v1) &*& this.x2 |-> v2;
  @*/
  
  //@ requires true;
  //@ ensures b_inv(v1, v2);
  public B(int v1, int v2) 
    
    
  {
    super(v1);
    this.x2 = v2;
    //@ close b_inv(v1, v2);
  }
}
class A {
  int x1;
  /*@
  predicate A_inv() = this.x1 |-> ?v;
  @*/
    
  public A(int v) 
  //@ requires this.x1 |-> _;
  //@ ensures this.A_inv();
    
    
  {
    super();
    x1 = v;
    //@ close A_inv();
  }
}

class B extends A
{ 
  int x2;
  /*@
  predicate B_inv() = A_inv() &*& this.x2 |-> ?v;
  @*/
  
  public B(int v1, int v2) 
  //@ requires this.x1 |-> _ &*& this.x2 |-> _;
  //@ ensures this.B_inv();
    
    
  {
    super(v1);
    //@ open A_inv();
    this.x2 = v2;
    //@ close A_inv();
    //@ close B_inv();
  }
}
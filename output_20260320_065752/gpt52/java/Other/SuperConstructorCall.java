class A {
  int x1;
  
  /*@
  predicate A_inv() = this.x1 |-> ?v;
  @*/
    
  public A(int v) 
  //@ requires true;
  //@ ensures this.A_inv();
    
    
  {
    super();
    this.x1 = v;
    //@ close A_inv();
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate B_inv() = this.A_inv() &*& this.x2 |-> ?v2;
  @*/
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures this.B_inv();
    
    
  {
    super(v1);
    //@ open A_inv();
    this.x2 = v2;
    //@ close B_inv();
  }
}
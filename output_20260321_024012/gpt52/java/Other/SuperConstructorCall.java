class A {
  int x1;
  /*@
  predicate A_inv(int v) = this.x1 |-> v;
  @*/
    
  public A(int v) 
  //@ requires this != null;
  //@ ensures A_inv(v);
    
    
  {
    super();
    //@ close A_inv(0);
    //@ open A_inv(_);
    x1 = v;
    //@ close A_inv(v);
  }
}

class B extends A
{ 
  int x2;
  /*@
  predicate B_inv(int v1, int v2) = A_inv(v1) &*& this.x2 |-> v2;
  @*/
  
  public B(int v1, int v2) 
  //@ requires this != null;
  //@ ensures B_inv(v1, v2);
    
    
  {
    super(v1);
    //@ close B_inv(v1, 0);
    //@ open B_inv(_, _);
    this.x2 = v2;
    //@ close B_inv(v1, v2);
  }
}
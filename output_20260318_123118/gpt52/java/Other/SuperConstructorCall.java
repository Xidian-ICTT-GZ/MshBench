class A {
  int x1;
  
  /*@ predicate a_inv(int v) = this.x1 |-> v; @*/
    
  public A(int v) 
  //@ requires this != null;
  //@ ensures a_inv(v);
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@ predicate b_inv(int v1, int v2) = a_inv(v1) &*& this.x2 |-> v2; @*/
  
  public B(int v1, int v2) 
  //@ requires this != null;
  //@ ensures b_inv(v1, v2);
  {
    super(v1);
    this.x2 = v2;
  }
}
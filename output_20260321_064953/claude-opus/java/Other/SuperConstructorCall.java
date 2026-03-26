class A {
  int x1;
  
  /*@
  predicate A_inv() = this |-> ?this0 &*& x1 |-> ?x1_val;
  @*/
  
  //@ requires true;
  //@ ensures A_inv();
  public A(int v) 
  {
    //@ close A_inv();
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate B_inv() = A_inv() &*& this |-> ?this0 &*& x2 |-> ?x2_val;
  @*/
  
  //@ requires true;
  //@ ensures B_inv();
  public B(int v1, int v2) 
  {
    //@ open A_inv();
    super(v1);
    this.x2 = v2;
    //@ close B_inv();
  }
}
class A {
  int x1;
  
  /*@ predicate A_inv() =
        this.x1 |-> _;
  @*/
  
  //@ requires true;
  //@ ensures A_inv();
  public A(int v) 
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@ predicate B_inv() =
        A_inv() &*&
        this.x2 |-> _;
  @*/
  
  //@ requires true;
  //@ ensures B_inv();
  public B(int v1, int v2) 
  {
    super(v1);
    this.x2 = v2;
  }
}
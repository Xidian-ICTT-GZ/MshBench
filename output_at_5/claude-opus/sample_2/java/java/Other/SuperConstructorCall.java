class A {
  int x1;
    
  /*@
  predicate inv() = this.x1 |-> _;
  @*/
    
  public A(int v) 
  //@ requires true;
  //@ ensures inv();
  {
    super();
    //@ close inv();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;

  /*@
  predicate inv() = this.x1 |-> _ &*& this.x2 |-> _;
  @*/
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures inv();
  {
    super(v1);
    //@ open inv();
    this.x2 = v2;
    //@ close inv();
  }
}
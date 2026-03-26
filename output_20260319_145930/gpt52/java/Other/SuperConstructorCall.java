class A {
  int x1;

  /*@ predicate A_state(int v) = this.x1 |-> v; @*/
    
  //@ requires true;
  //@ ensures A_state(v);
  public A(int v) 
  {
    super();
    this.x1 = v;
    //@ close A_state(v);
  }
}

class B extends A
{ 
  int x2;

  /*@ predicate B_state(int v1, int v2) = A_state(v1) &*& this.x2 |-> v2; @*/
  
  //@ requires true;
  //@ ensures B_state(v1, v2);
  public B(int v1, int v2) 
  {
    //@ open A_state(v1);
    super(v1);
    this.x2 = v2;
    //@ close B_state(v1, v2);
  }
}
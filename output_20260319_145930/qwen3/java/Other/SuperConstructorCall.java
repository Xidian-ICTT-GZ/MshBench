class A {
  int x1;
    
  /*@
  predicate_ctor A(int v) = x1 |-> v;
  @*/
    
  public A(int v) 
  //@ requires true;
  //@ ensures A(v);
  {
    super();
    x1 = v;
    //@ close A(v);
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate_ctor B(int v1, int v2) = A(v1) &*& x2 |-> v2;
  @*/
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures B(v1, v2);
  {
    super(v1);
    this.x2 = v2;
    //@ close B(v1, v2);
  }
}
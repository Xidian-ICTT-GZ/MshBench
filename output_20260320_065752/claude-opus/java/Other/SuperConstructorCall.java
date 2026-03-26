class A {
  int x1;
  
  /*@
  predicate objectA(A this) = this.x1 |-> ?_x1;
  @*/
    
  public A(int v)
  //@ requires true;
  //@ ensures objectA(this) &*& x1 == v;
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate objectB(B this) = objectA(this) &*& this.x2 |-> ?_x2;
  @*/
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures objectB(this) &*& x1 == v1 &*& x2 == v2;
  {
    super(v1);
    this.x2 = v2;
  }
}
class A {
  int x1;
    
  /*@
  predicate A_pred(int v) = x1 |-> v;
  @*/
    
  public A(int v) 
    
    
  {
    //@ close A_pred(v);
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@
  predicate B_pred(int v1, int v2) = A_pred(v1) &*& x2 |-> v2;
  @*/
  
  public B(int v1, int v2) 
    
    
  {
    //@ open A_pred(v1);
    super(v1);
    this.x2 = v2;
    //@ close B_pred(v1, v2);
  }
}
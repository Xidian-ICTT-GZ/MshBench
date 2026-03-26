class A {
  int x1;
    
  //@ predicate A(int x) = this.x1 |-> x;
    
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
  
  //@ predicate B(int x1, int x2) = A(x1) &*& this.x2 |-> x2;
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures B(v1, v2);
  {
    super(v1);
    this.x2 = v2;
    //@ close B(v1, v2);
  }
}
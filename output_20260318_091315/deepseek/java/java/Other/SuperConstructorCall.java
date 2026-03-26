class A {
  int x1;
    
  //@ predicate valid() = this.x1 |-> ?v;
    
  public A(int v) 
  //@ requires true;
  //@ ensures valid();
  {
    super();
    x1 = v;
    //@ close valid();
  }
}

class B extends A
{ 
  int x2;
  
  //@ predicate valid() = super.valid() &*& this.x2 |-> ?v;
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures valid();
  {
    super(v1);
    this.x2 = v2;
    //@ close valid();
  }
}
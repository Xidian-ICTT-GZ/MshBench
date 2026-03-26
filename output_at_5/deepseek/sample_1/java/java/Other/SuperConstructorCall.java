class A {
  int x1;
  //@ predicate A() = x1 |-> ?v;
    
  public A(int v) 
  //@ requires true;
  //@ ensures A();
    
    
  {
    super();
    //@ close A();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  //@ predicate B() = A() &*& x2 |-> ?v;
  
  public B(int v1, int v2) 
  //@ requires true;
  //@ ensures B();
    
    
  {
    super(v1);
    //@ open A();
    this.x2 = v2;
    //@ close B();
  }
}
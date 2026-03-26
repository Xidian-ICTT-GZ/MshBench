class A {
  int x1;
  //@ predicate A() = x1 |-> ?v;
    
  public A(int v) 
  //@ requires true;
  //@ ensures A();
    
    
  {
    super();
    x1 = v;
    //@ close A();
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
    this.x2 = v2;
    //@ close B();
  }
}
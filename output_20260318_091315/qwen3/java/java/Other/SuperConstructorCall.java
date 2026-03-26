/*@ predicate A(int v1) = this.x1 |-> v1; @*/
/*@ predicate B(int v1, int v2) = A(v1) &*& this.x2 |-> v2; @*/

class A {
  int x1;
    
  //@ requires true;
  //@ ensures A(v);
  public A(int v) 
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  //@ requires true;
  //@ ensures B(v1, v2);
  public B(int v1, int v2) 
  {
    super(v1);
    this.x2 = v2;
  }
}
/*@ predicate A_pred(A a; int v) = a.x1 |-> v; @*/
/*@ predicate B_pred(B b; int v1, int v2) = A_pred(b, v1) &*& b.x2 |-> v2; @*/

class A {
  int x1;
    
  //@ requires true;
  //@ ensures A_pred(this, v);
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
  //@ ensures B_pred(this, v1, v2);
  public B(int v1, int v2) 
  {
    super(v1);
    this.x2 = v2;
  }
}
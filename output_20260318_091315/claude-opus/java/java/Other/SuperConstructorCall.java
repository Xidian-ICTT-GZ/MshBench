class A {
  int x1;
  
  /*@ predicate objectA(A a; int v) = a.x1 |-> v; @*/
  
  //@ requires true;
  //@ ensures objectA(this) &*& x1 == v;
  public A(int v) 
  {
    super();
    x1 = v;
  }
}

class B extends A
{ 
  int x2;
  
  /*@ predicate objectB(B b; int v1, int v2) = 
        this.objectA(v1) &*& b.x2 |-> v2; @*/
  
  //@ requires true;
  //@ ensures objectB(this, v1, v2) &*& x1 == v1 &*& x2 == v2;
  public B(int v1, int v2) 
  {
    super(v1);
    this.x2 = v2;
  }
}
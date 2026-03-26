abstract class A {
  
  /*@
  predicate A_object(this) = true;
  @*/
  
  //@ public abstract void m();
  public abstract void m();
    
}

class B extends A {
  int x;
  
  /*@
  predicate B_object(this; int xVal) = this.x |-> xVal &*& A_object(this);
  @*/
  
  //@ requires B_object(this, ?x0);
  //@ ensures B_object(this, 0);
  public void m()
  {
    //@ open B_object(this, _);
    x = 0;
    //@ close B_object(this, 0);
  }
}

abstract class B2 extends A {
  /*@
  predicate B2_object(this) = A_object(this);
  @*/
}

class Program {
  /*@
  predicate Program_object(this) = true;
  @*/
  
  //@ requires A_object(a);
  //@ ensures A_object(a);
  public void test(A a) 
  {
    a.m();
  }
}
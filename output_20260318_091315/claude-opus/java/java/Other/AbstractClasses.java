abstract class A {
  
  /*@ 
    predicate objectA() = this.A_m_inv();

    predicate A_m_inv();

    //@ requires objectA();
    //@ ensures objectA();
  @*/
  public abstract void m();
    
}

class B extends A {
  int x;
  
  /*@ 
    predicate objectB(int v) = this.x |-> v;

    //@ predicate A_m_inv() = objectB(?v);

    //@ requires objectB(?v);
    //@ ensures objectB(0);
  @*/
  public void m()
  {
    x = 0;
  }
}

abstract class B2 extends A {
  /*@ 
    //@ predicate A_m_inv();
  @*/
}

class Program {
  /*@
    //@ requires a.objectA();
    //@ ensures a.objectA();
  @*/
  public void test(A a)
  {
    a.m();
  }
}
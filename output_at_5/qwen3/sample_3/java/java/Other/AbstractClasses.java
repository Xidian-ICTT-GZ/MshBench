abstract class A {
  public abstract void m();
    
}

class B extends A {
  int x;
  
  public void m()
    //@ requires true;
    //@ ensures true;
  {
    x = 0;
  }
}

abstract class B2 extends A {
}

class Program {
  public void test(A a) 
    //@ requires a != null;
    //@ ensures true;
  {
    a.m();
  }
}
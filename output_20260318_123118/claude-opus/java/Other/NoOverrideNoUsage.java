abstract class A 
{
  /*@ predicate validA() = true; @*/

  //@ requires true;
  //@ ensures validA();
  public A()
  {
  }

  //@ requires validA();
  //@ ensures validA();
  public void m()
  {
  }
}

class B extends A 
{
  /*@ predicate validB() = validA() &*& this::m(){}; @*/

  //@ requires true;
  //@ ensures validB();
  public B()
  {
    super();
  }
}

class C 
{
  //@ requires true;
  //@ ensures true;
  public void m()
  {
    B b = new B();
  }
}
/*@ predicate A() @*/

/*@ predicate B() = A(); @*/

abstract class A 
{
  //@ requires true;
  //@ ensures A();
  public A()
  {
  }

  //@ requires A();
  //@ ensures A();
  public void m()
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures B();
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
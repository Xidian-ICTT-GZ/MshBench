abstract class A 
{
  /*@
  predicate_family_instance object(A a) = true;
  @*/

  //@ requires true;
  //@ ensures object(this);
  public A()
  {
  }

  //@ requires object(this);
  //@ ensures object(this);
  public void m()
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures object(this);
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
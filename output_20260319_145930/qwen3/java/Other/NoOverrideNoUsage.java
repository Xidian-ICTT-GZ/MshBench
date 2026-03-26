abstract class A 
{
  /*@ predicate_family_instance object(A a); @*/

  //@ requires true;
  //@ ensures object(this);
  public A()
  {
    //@ close object(this);
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
    //@ open object(this);
    //@ close object(this);
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
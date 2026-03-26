abstract class A 
{
  //@ predicate_family_instance object(A a) = true;

  public A()
  //@ requires true;
  //@ ensures object(this);
  {
    //@ close object(this);
  }

  public void m()
  //@ requires object(this);
  //@ ensures object(this);
  {
  }
}

class B extends A
{
  //@ predicate_family_instance object(B b) = object((A)b);

  public B()
  //@ requires true;
  //@ ensures object(this);
  {
    super();
    //@ open object((A)this);
    //@ close object(this);
  }
}

class C 
{
  public void m()
  //@ requires true;
  //@ ensures true;
  {
    B b = new B();
    //@ open object(b);
  }
}
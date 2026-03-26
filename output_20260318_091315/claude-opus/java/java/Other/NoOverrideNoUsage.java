abstract class A 
{
  /*@ 
    predicate object_pred(A a) = true;
  @*/

  //@ requires true;
  //@ ensures object_pred(this);
  public A()
  {
  }

  //@ requires object_pred(this);
  //@ ensures object_pred(this);
  public void m()
  {
  }
}

class B extends A 
{
  /*@ 
    predicate object_pred(B b) = object_pred((A)b);
  @*/

  //@ requires true;
  //@ ensures object_pred(this);
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
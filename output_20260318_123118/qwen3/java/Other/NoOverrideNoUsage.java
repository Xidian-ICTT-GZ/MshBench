//@ predicate A_pred(A a;) = true;

abstract class A 
{
  //@ requires true;
  //@ ensures A_pred(this);
  public A()
  {
  }

  //@ requires A_pred(this);
  //@ ensures A_pred(this);
  public void m()
  {
  }
}

class B extends A 
{
  //@ requires true;
  //@ ensures A_pred(this);
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
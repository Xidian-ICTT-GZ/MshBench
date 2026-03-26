/*@ predicate A_inv(A a;) = true; @*/

abstract class A 
{
  //@ requires true;
  //@ ensures A_inv(this);
  public A()
  {
  }

  //@ requires A_inv(this);
  //@ ensures A_inv(this);
  public void m()
  {
  }
}

class B extends A
{
  //@ requires true;
  //@ ensures A_inv(this);
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
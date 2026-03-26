abstract class A 
{
  /*@ predicate a() = this != null; @*/

  public A()
  //@ requires true;
  //@ ensures a();
  {
  }

  public void m()
  //@ requires a();
  //@ ensures a();
  {
  }
}

class B extends A
{
  /*@ predicate b() = this != null &*& a(); @*/

  public B()
  //@ requires true;
  //@ ensures b();
  {
    super();
  }
}

class C 
{
  /*@ predicate c() = this != null; @*/

  public void m()
  //@ requires c();
  //@ ensures c();
  {
    B b = new B();
    //@ open b();
    //@ open a();
  }
}
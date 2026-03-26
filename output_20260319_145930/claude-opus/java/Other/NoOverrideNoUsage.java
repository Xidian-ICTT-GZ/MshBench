abstract class A 
{
  //@ predicate A() = true;

  public A()
    //@ requires true;
    //@ ensures A();
  {
    //@ close A();
  }

  public void m()
    //@ requires A();
    //@ ensures A();
  {
  }
}

class B extends A 
{
  //@ predicate B() = A();

  public B()
    //@ requires true;
    //@ ensures B();
  {
    super();
    //@ close B();
  }
}

class C 
{
  public void m()
    //@ requires true;
    //@ ensures true;
  {
    B b = new B();
  }
}
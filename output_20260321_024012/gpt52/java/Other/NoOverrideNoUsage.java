abstract class A 
{
  /*@
  predicate A_inv() = true;
  @*/

  public A()
  //@ requires true;
  //@ ensures A_inv();
  {
    //@ close A_inv();
  }

  public void m()
  //@ requires A_inv();
  //@ ensures A_inv();
  {
  }
}

class B extends A 
{
  /*@
  predicate B_inv() = A_inv();
  @*/

  public B()
  //@ requires true;
  //@ ensures B_inv();
  {
    super();
    //@ close B_inv();
  }
}

class C 
{
  public void m()
  //@ requires true;
  //@ ensures true;
  {
    B b = new B();
    //@ open B_inv();
  }
}
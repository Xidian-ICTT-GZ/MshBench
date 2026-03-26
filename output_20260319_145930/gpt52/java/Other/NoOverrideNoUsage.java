abstract class A 
{
  /*@
  predicate A_inv() = this != null;
  @*/

  //@ requires true;
  //@ ensures A_inv();
  public A()
  {
    //@ close A_inv();
  }

  //@ requires A_inv();
  //@ ensures A_inv();
  public void m()
  {
  }
}

class B extends A 
{
  /*@
  predicate B_inv() = this != null &*& A_inv();
  @*/

  //@ requires true;
  //@ ensures B_inv();
  public B()
  {
    super();
    //@ close B_inv();
  }
}

class C 
{
  /*@
  predicate C_inv() = this != null;
  @*/

  //@ requires true;
  //@ ensures C_inv();
  public C()
  {
    //@ close C_inv();
  }

  //@ requires C_inv();
  //@ ensures C_inv();
  public void m()
  {
    B b = new B();
    //@ open B_inv();
    //@ open A_inv();
  }
}
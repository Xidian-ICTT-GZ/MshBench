abstract class A 
{
  /*@ predicate A_inv() = true; @*/

  //@ requires true;
  //@ ensures A_inv();
  public A()
  {
  }

  //@ requires A_inv();
  //@ ensures A_inv();
  public void m()
  {
  }
}

class B extends A
{
  /*@ predicate B_inv() = A_inv(); @*/

  //@ requires true;
  //@ ensures B_inv();
  public B()
  {
    //@ close A_inv();
    super();
    //@ close B_inv();
  }
}

class C 
{
  //@ requires true;
  //@ ensures true;
  public void m()
  {
    B b = new B();
    //@ open b.B_inv();
  }
}
abstract class A 
{
  /*@
    predicate A_inv()
    ;
  @*/

  //@ public instance void m()
  //@ requires this.A_inv();
  //@ ensures this.A_inv();
  public A()
  //@ requires true;
  //@ ensures this.A_inv();
  {
  }

  //@ public void m()
  //@ requires this.A_inv();
  //@ ensures this.A_inv();
  public void m()
  {
  }
}

class B extends A
{
  //@ public instance void m()
  //@ requires this.A_inv();
  //@ ensures this.A_inv();
  public B()
  //@ requires true;
  //@ ensures this.A_inv();
  {
    super();
  }
}

class C 
{
  //@ public void m()
  //@ requires true;
  //@ ensures true;
  public void m()
  {
    B b = new B();
  }
}
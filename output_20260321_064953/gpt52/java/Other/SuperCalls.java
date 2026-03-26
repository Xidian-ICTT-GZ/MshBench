class A {
  int x;

  /*@
  predicate AInv() = this.x |-> ?v;
  @*/

  public int m(int y) 
    //@ requires this.AInv();
    //@ ensures this.AInv() &*& result == y;
  {
    //@ open AInv();
    x = y;
    //@ close AInv();
    return y;
  }

  
}

class B extends A {
  

  public int m(int y) 
    //@ requires this.AInv();
    //@ ensures this.AInv() &*& result == y;
  {
    int tmp = super.m(y);
   return tmp;
  }
}
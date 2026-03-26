class C {
  final static int f = 10;
  
  /*@
    predicate valid_c(C this;) = true;
  @*/
  
  void m()
    //@ requires valid_c(this);
    //@ ensures valid_c(this);
  {
    short x = 20 + f;
  }
}
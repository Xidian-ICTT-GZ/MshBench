class C {
  final static int f = 10;
  
  /*@
  predicate this_inv() = true;
  @*/
  
  void m()
  //@ requires this_inv();
  //@ ensures this_inv();
  {
    short x = 20 + f;
  }
}
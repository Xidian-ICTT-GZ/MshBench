class C {
  final static int f = 10;
  
  //@ requires true;
  //@ ensures true;
  void m()
    
    
  {
    //@ close C_f();
    short x = 20 + f;
    
  }
  
  /*@
  predicate C_f() = f |-> 10;
  @*/
}
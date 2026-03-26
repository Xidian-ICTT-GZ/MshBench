class C {
  final static int f = 10;
  
  //@ requires true;
  //@ ensures true;
  void m()
    
    
  {
    //@ close Class_C();
    short x = 20 + f;
    //@ open Class_C();
    
  }
  
  //@ predicate Class_C() = true;
}
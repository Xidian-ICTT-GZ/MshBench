class C {
  final static int f = 10;
  
  //@ requires true
  //@ ensures true
  void m()
  {
    short x = 20 + f;
    
  }
}
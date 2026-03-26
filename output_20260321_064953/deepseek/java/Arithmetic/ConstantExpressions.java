class C {
  final static int f = 10;
  
  //@ requires true;
  //@ ensures true;
  void m()
    
    
  {
    //@ close true;
    short x = 20 + f;
    //@ open true;
    
  }
}
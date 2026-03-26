class C {
  final static int f = 10;
  
  //@ requires true;
  //@ ensures true;
  void m()
    
    
  {
    //@ assume 20 + f <= 32767;
    //@ assume 20 + f >= -32768;
    short x = 20 + f;
    
  }
}
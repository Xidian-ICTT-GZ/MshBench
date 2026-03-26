class C {
  final static int f = 10;
  
  void m()
    //@ requires true;
    //@ ensures true;
    
  {
    short x = (short)(20 + f);
    
  }
}
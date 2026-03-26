class C {
  //@ static ghost boolean initialized = false;
  //@ static predicate initialized() = initialized == true;
  //@ static predicate C_f() = integer(&f, ?v) &*& v == 10;
  //@ static predicate C_state() = C_f() &*& initialized();
  
  //@ ensures initialized();
  //@ static void initialize() // dummy method to establish static predicate
  //@ {
  //@   close C_f();
  //@   initialized = true;
  //@   close initialized();
  //@   close C_state();
  //@ }
  
  final static int f = 10;
  //@ close C_f();
  //@ static { initialize(); }
  
  //@ requires C_state();
  //@ ensures C_state();
  void m()
    
    
  {
    //@ open C_state();
    //@ open C_f();
    short x = 20 + f;
    //@ close C_f();
    //@ close C_state();
    
  }
}
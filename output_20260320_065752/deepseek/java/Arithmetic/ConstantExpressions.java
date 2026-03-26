class C {
  //@ static ghost int f_ghost = 10;
  final static int f = 10;
  //@ static predicate C_f() = f |-> ?v &*& v == 10;
  
  //@ requires true;
  //@ ensures true;
  void m()
    
    
  {
    //@ close C_f();
    short x = 20 + f;
    //@ open C_f();
    
  }
}
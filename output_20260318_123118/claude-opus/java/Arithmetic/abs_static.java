class Program {
  
  /*@ predicate abs_input(short x) = true; @*/
  /*@ predicate abs_result(short r) = r >= 0 &*& r <= 32767; @*/
  
  //@ requires abs_input(x);
  //@ ensures abs_result(result);
  static short abs(short x)
  {
    if (x < 0) {
      x = (short)-x;
      return x;
    } else {
      return x;
    }
  }
}
class Program {
  /*@ predicate abs_parameter(short x) = true; @*/

  //@ requires abs_parameter(x);
  //@ ensures abs_parameter(result);
  //@ ensures result >= 0;
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
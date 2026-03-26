class Program {
  /*@ 
    predicate abs_pre(short x) = true;
    predicate abs_post(short x, short result) = result >= 0 &*& 
      (x < 0 ==> result == (short) (-x)) &*&
      (x >= 0 ==> result == x);
  @*/

  //@ requires abs_pre(x);
  //@ ensures abs_post(x, result);
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
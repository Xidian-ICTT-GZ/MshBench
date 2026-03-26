class Program {
  /*@
    predicate_abs(short x) = true;
  @*/

  //@ requires true;
  /*@ ensures
        (x < 0 ==> result == (short)(-x)) &*&
        (x >= 0 ==> result == x);
  @*/
  static short abs(short x) {
    if (x < 0) {
      x = (short) -x;
      return x;
    } else {
      return x;
    }
  }
}
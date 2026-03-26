class Program {
  /*@ predicate abs_short_value(short x, int v) = (x >= 0 &*& v == x) || (x < 0 &*& v == -x); @*/

  //@ requires true;
  //@ ensures abs_short_value(x, result);
  static int abs(short x)
  {
    if (x < 0)
      return -x;
    else
      return x;
  }
}
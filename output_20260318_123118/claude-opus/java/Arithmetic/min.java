class Program {
  /*@ predicate validShortValue(short v) = true; @*/

  //@ requires validShortValue(x) &*& validShortValue(y) &*& validShortValue(z);
  //@ ensures validShortValue(result) &*& (result <= x || result <= y) &*& (result <= z);
  static short min(short x, short y, short z)
  {
    short m = x < y ? x : y;
    m = m < z ? m : z;
    return m;
  }
}